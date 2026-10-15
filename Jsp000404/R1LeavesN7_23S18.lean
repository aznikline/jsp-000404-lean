import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_23S17

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5172000 in
set_option maxHeartbeats 5172000 in
theorem r1l7_12_24_L_I_M_IR_s3_x1_x1_x0_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3260 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4130 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h4359 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4559 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3260 := hg3260
  rcases m.htr 0 2 5 (by decide) (by decide) with h5817 | h5817
  · rcases m.htr 0 3 4 (by decide) (by decide) with h5818 | h5818
    · linarith only [h4558, h4559, h5818, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h5820 | h5820
      · rcases m.htr 1 2 3 (by decide) (by decide) with h5821 | h5821
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5822 | h5822
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5823 | h5823
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5824 | h5824
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5825 | h5825
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5826 | h5826
                  · linarith only [h4558, h4559, h5818, h5822, h5826, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5828 | h5828
                    · linarith only [h4558, h4559, h5821, h5824, h5826, h5828, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5830 | h5830
                      · linarith only [h4559, h5817, h5821, h5824, h5826, h5830, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h4559, h5817, h5820, h5828, h5830, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h4559, h5818, h5820, h5821, h5822, h5824, h5825, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5834 | h5834
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5835 | h5835
                  · linarith only [h0, h4130, h4558, h5824, h5835, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5837 | h5837
                    · linarith only [h4558, h4559, h5822, h5837, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5839 | h5839
                      · linarith only [h4559, h5817, h5822, h5839, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h4559, h5817, h5820, h5837, h5839, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h4559, h5817, h5820, h5822, h5834, hlam]
            · linarith only [h4559, h5817, h5822, h5823, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5844 | h5844
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5845 | h5845
              · linarith only [h3260, h5818, h5821, h5822, h5845, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5847 | h5847
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5848 | h5848
                  · linarith only [h3260, h5845, h5848, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5850 | h5850
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5851 | h5851
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5852 | h5852
                        · linarith only [h0, h4558, h5822, h5848, h5850, h5852, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                        · linarith only [h0, h4558, h5822, h5848, h5850, h5851, h5852, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h4558, h5820, h5822, h5851, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5856 | h5856
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5857 | h5857
                        · rcases h2bigk with h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c | h5858c
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [hlam, p5858_0]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [h0, hlam, p5858_0]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [h4559, h5848, hc23, hc34, hlam, hphi, p5858_1]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [h4559, hlam, p5858_0]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [h4559, h5848, h5856, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5858_1, u4ehi4]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [h5817, h5856, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5858_1, u4ehi4]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [hlam, p5858_0]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [h5822, h5848, hc23, hc34, hlam, hphi, p5858_1]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [h5822, hlam, p5858_0]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [h5822, h5848, h5856, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5858_1, u4ehi4]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [h4558, hlam, p5858_0]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [h5821, hlam, p5858_0]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [hlam, p5858_0]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [h5848, hlam, p5858_1]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [h5850, hlam, p5858_1]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [h5817, h5848, h5856, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p5858_1, u4ehi4]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [h3260, h5821, h5848, hc01, hc34, hlam, hphi, ht12, ht23, p5858_1]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            rcases p5858_3 (m.d 0 2) (by simp) with h5876 | h5876
                            · linarith only [h4559, h5876, hlam]
                            · linarith only [h4558, h5876, hlam]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [hlam, p5858_0]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            rcases p5858_3 (m.d 0 2) (by simp) with h5880 | h5880
                            · linarith only [h4559, h5880, hlam]
                            · linarith only [h5817, h5880, hlam]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [h5817, hlam, p5858_0]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [h5844, hlam, p5858_0]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [h4559, h5817, h5848, hc23, hc34, hlam, hphi, p5858_1]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [h5856, hlam, p5858_1]
                          · have p5858_0 := h5858c.1
                            have p5858_1 := h5858c.2.1
                            have p5858_2 := h5858c.2.2.1
                            have p5858_3 := h5858c.2.2.2
                            linarith only [hlam, p5858_0]
                        · linarith only [h0, h5822, h5848, h5857, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h4359, h5820, h5822, h5844, h5856, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                · linarith only [h4130, h4559, h5817, h5820, h5847, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h0, h5817, h5844, hlam]
        · linarith only [h0, h4558, h5821, hlam]
      · linarith only [h4559, h5817, h5820, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h5894 | h5894
    · linarith only [h4558, h4559, h5894, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h5896 | h5896
      · rcases m.htr 1 2 3 (by decide) (by decide) with h5897 | h5897
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5898 | h5898
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5899 | h5899
            · rcases m.htr 1 3 4 (by decide) (by decide) with h5900 | h5900
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5901 | h5901
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5902 | h5902
                  · linarith only [h3260, h4558, h4559, h5894, h5898, h5902, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5904 | h5904
                    · linarith only [h4558, h4559, h5897, h5900, h5902, h5904, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5906 | h5906
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5907 | h5907
                        · rcases h2bigk with h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c | h5908c
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [hlam, p5908_0]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [h0, hlam, p5908_0]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [h5817, h5897, h5900, h5902, h5906, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5908_1]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [h4559, hlam, p5908_0]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [h5817, hlam, p5908_0]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            rcases p5908_3 (m.d 0 2) (by simp) with h5914 | h5914
                            · linarith only [h0, h5914, hlam]
                            · rcases p5908_3 (m.d 1 2) (by simp) with h5916 | h5916
                              · rcases p5908_3 (m.d 2 3) (by simp) with h5917 | h5917
                                · linarith only [h5897, h5917, hlam]
                                · rcases p5908_3 (m.d 2 4) (by simp) with h5919 | h5919
                                  · linarith only [h5898, h5919, hlam]
                                  · linarith only [h4559, h5919, hlam]
                              · linarith only [h0, h5916, hlam]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [hlam, p5908_0]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [h4558, h5817, h5897, h5900, h5902, h5906, hlam, p5908_2]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [h4558, h5817, h5906, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5908_1]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [h4558, h5817, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5908_1]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [h4558, hlam, p5908_0]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [h5897, hlam, p5908_0]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [hlam, p5908_0]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [h5902, hlam, p5908_1]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [h5904, hlam, p5908_1]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [h4558, h5898, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5908_1]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [h5898, hlam, p5908_0]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            rcases p5908_3 (m.d 0 2) (by simp) with h5934 | h5934
                            · linarith only [h4559, h5934, hlam]
                            · linarith only [h4558, h5934, hlam]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [hlam, p5908_0]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [h4558, h5817, h5897, h5900, h5902, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5908_1]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [h4558, h5904, hc23, hc35, hlam, hphi, p5908_1]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [h5899, hlam, p5908_0]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            rcases p5908_3 (m.d 0 2) (by simp) with h5941 | h5941
                            · linarith only [h5817, h5941, hlam]
                            · linarith only [h4558, h5941, hlam]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [h5906, hlam, p5908_1]
                          · have p5908_0 := h5908c.1
                            have p5908_1 := h5908c.2.1
                            have p5908_2 := h5908c.2.2.1
                            have p5908_3 := h5908c.2.2.2
                            linarith only [hlam, p5908_0]
                        · linarith only [h4130, h4558, h4559, h5896, h5902, h5907, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h4559, h5896, h5906, hlam]
                · linarith only [h4130, h4559, h5896, h5901, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h5949 | h5949
                · rcases m.htr 2 3 4 (by decide) (by decide) with h5950 | h5950
                  · linarith only [h3260, h4558, h5900, h5950, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h5952 | h5952
                    · linarith only [h4558, h4559, h5898, h5952, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h5954 | h5954
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h5955 | h5955
                        · rcases h2bigk with h5956c | h5956c | h5956c | h5956c | h5956c | h5956c | h5956c | h5956c | h5956c | h5956c | h5956c | h5956c | h5956c | h5956c | h5956c | h5956c | h5956c | h5956c | h5956c | h5956c | h5956c | h5956c | h5956c | h5956c | h5956c
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [hlam, p5956_0]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [h0, hlam, p5956_0]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [h5817, h5898, h5954, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5956_1]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [h4559, hlam, p5956_0]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [h5817, hlam, p5956_0]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            rcases p5956_3 (m.d 0 2) (by simp) with h5962 | h5962
                            · linarith only [h0, h5962, hlam]
                            · rcases p5956_3 (m.d 1 2) (by simp) with h5964 | h5964
                              · rcases p5956_3 (m.d 2 3) (by simp) with h5965 | h5965
                                · linarith only [h5897, h5965, hlam]
                                · rcases p5956_3 (m.d 2 4) (by simp) with h5967 | h5967
                                  · linarith only [h5898, h5967, hlam]
                                  · linarith only [h4559, h5967, hlam]
                              · linarith only [h0, h5964, hlam]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [hlam, p5956_0]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [h4558, h5817, h5898, h5954, hlam, p5956_2]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [h4559, h5896, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p5956_1, u4ehi4]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [h4558, h5817, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5956_1]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [h4558, hlam, p5956_0]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [h5897, hlam, p5956_0]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [hlam, p5956_0]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [h5950, hlam, p5956_1]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [h5952, hlam, p5956_1]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [h4558, h5898, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5956_1]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [h5898, hlam, p5956_0]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            rcases p5956_3 (m.d 0 2) (by simp) with h5982 | h5982
                            · linarith only [h4559, h5982, hlam]
                            · linarith only [h4558, h5982, hlam]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [hlam, p5956_0]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [h4558, h5817, h5898, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p5956_1]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [h4558, h5952, hc23, hc35, hlam, hphi, p5956_1]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [h5899, hlam, p5956_0]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            rcases p5956_3 (m.d 0 2) (by simp) with h5989 | h5989
                            · linarith only [h5817, h5989, hlam]
                            · linarith only [h4558, h5989, hlam]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [h5954, hlam, p5956_1]
                          · have p5956_0 := h5956c.1
                            have p5956_1 := h5956c.2.1
                            have p5956_2 := h5956c.2.2.1
                            have p5956_3 := h5956c.2.2.2
                            linarith only [hlam, p5956_0]
                        · linarith only [h3260, h5896, h5900, h5955, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                      · linarith only [h4559, h5896, h5954, hlam]
                · linarith only [h4559, h5896, h5898, h5949, hlam]
            · linarith only [h4559, h5896, h5898, h5899, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h5998 | h5998
            · linarith only [h4558, h5817, h5898, h5998, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6000 | h6000
              · linarith only [h5894, h5896, h5897, h5898, h6000, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h6002 | h6002
                · rcases m.htr 2 3 4 (by decide) (by decide) with h6003 | h6003
                  · linarith only [h0, h4558, h5898, h6000, h6003, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h6005 | h6005
                    · linarith only [h0, h4558, h5998, h6005, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6007 | h6007
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h6008 | h6008
                        · rcases h2bigk with h6009c | h6009c | h6009c | h6009c | h6009c | h6009c | h6009c | h6009c | h6009c | h6009c | h6009c | h6009c | h6009c | h6009c | h6009c | h6009c | h6009c | h6009c | h6009c | h6009c | h6009c | h6009c | h6009c | h6009c | h6009c
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [hlam, p6009_0]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [h0, hlam, p6009_0]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [h0, h5998, h6003, h6007, hc23, hc34, hlam, hphi, p6009_1]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [h4559, hlam, p6009_0]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [h5817, hlam, p6009_0]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [h5998, h6003, h6007, hc02, hc34, hlam, hphi, ht23, p6009_1]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [hlam, p6009_0]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [h5998, h6003, h6007, hc23, hc34, hlam, hphi, p6009_1]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [h5898, hlam, p6009_0]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [h5998, hlam, p6009_0]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [h4558, hlam, p6009_0]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [h5897, hlam, p6009_0]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [hlam, p6009_0]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [h6003, hlam, p6009_1]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [h6005, hlam, p6009_1]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [h4558, h6003, hc23, hc34, hlam, hphi, p6009_1]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [h0, h6003, hc01, hc34, hlam, hphi, ht12, ht23, p6009_1]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            rcases p6009_3 (m.d 0 2) (by simp) with h6027 | h6027
                            · linarith only [h4559, h6027, hlam]
                            · linarith only [h4558, h6027, hlam]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [hlam, p6009_0]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [h4558, h5817, h6003, hc23, hc34, hlam, hphi, p6009_1]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [h4558, h6005, h6008, hc23, hc34, hlam, hphi, p6009_1]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [h3260, h5897, hc01, hc25, hlam, hphi, ht12, p6009_1]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            rcases p6009_3 (m.d 0 2) (by simp) with h6034 | h6034
                            · linarith only [h5817, h6034, hlam]
                            · linarith only [h4558, h6034, hlam]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [h6007, hlam, p6009_1]
                          · have p6009_0 := h6009c.1
                            have p6009_1 := h6009c.2.1
                            have p6009_2 := h6009c.2.2.1
                            have p6009_3 := h6009c.2.2.2
                            linarith only [hlam, p6009_0]
                        · linarith only [h4558, h4559, h5896, h6003, h6008, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · linarith only [h4130, h5896, h5898, h6007, hlam]
                · linarith only [h4130, h5896, h6002, hlam]
        · linarith only [h0, h4558, h5897, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h6043 | h6043
        · rcases m.htr 1 2 4 (by decide) (by decide) with h6044 | h6044
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6045 | h6045
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6046 | h6046
              · rcases m.htr 1 4 5 (by decide) (by decide) with h6047 | h6047
                · rcases m.htr 2 3 4 (by decide) (by decide) with h6048 | h6048
                  · linarith only [h4558, h4559, h5894, h5896, h6043, h6046, h6047, h6048, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h6050 | h6050
                    · linarith only [h4558, h4559, h5896, h6043, h6046, h6047, h6050, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6052 | h6052
                      · linarith only [h4558, h4559, h5896, h6048, h6052, hc23, hc34, hlam, hphi]
                      · linarith only [h4558, h4559, h6043, h6046, h6047, h6052, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h4558, h4559, h6044, h6047, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h6056 | h6056
                · linarith only [h4558, h4559, h5896, h6046, h6056, hc23, hc34, hlam, hphi]
                · linarith only [h4558, h4559, h6044, h6056, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h4558, h4559, h6044, h6045, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6060 | h6060
            · linarith only [h4558, h5817, h6044, h6060, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6062 | h6062
              · linarith only [h3260, h5894, h6043, h6044, h6062, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h6064 | h6064
                · linarith only [h4558, h4559, h5896, h6062, h6064, hc23, hc34, hlam, hphi]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h6066 | h6066
                  · linarith only [h0, h4558, h6044, h6064, h6066, hc45, hlam, hphi, u4ehi3]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h6068 | h6068
                    · linarith only [h0, h4359, h4558, h6044, h6060, h6064, h6068, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h6070 | h6070
                      · linarith only [h0, h4558, h6044, h6064, h6066, h6070, hc23, hc34, hlam, hphi]
                      · linarith only [h4558, h4559, h6070, hc23, hc45, hlam, hphi, ht34]
        · linarith only [h4558, h4559, h6043, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 5172000 in
set_option maxHeartbeats 5172000 in
theorem r1l7_12_24_L_I_M_IR_s3_x1_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3260 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4130 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h4359 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4558 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3260 := hg3260
  rcases m.htr 0 2 4 (by decide) (by decide) with h4559 | h4559
  · exact r1l7_12_24_L_I_M_IR_s3_x1_x1_x0_x0 m hb2 hb4 hg0 hg3260 h4130 h4359 h4558 h4559
  · exact r1l7_12_24_L_I_M_IR_s3_x1_x1_x0_x1 m hb2 hb4 hg0 hg3260 h4130 h4359 h4558 h4559

set_option maxHeartbeats 5172000 in
set_option maxHeartbeats 5172000 in
theorem r1l7_12_24_L_I_M_IR_s3_x1_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3260 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4130 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h4359 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h4558 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3260 := hg3260
  rcases m.htr 0 2 4 (by decide) (by decide) with h6074 | h6074
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6075 | h6075
    · rcases m.htr 0 3 4 (by decide) (by decide) with h6076 | h6076
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6077 | h6077
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6078 | h6078
          · linarith only [h4558, h6074, h6078, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6080 | h6080
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6081 | h6081
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6082 | h6082
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6083 | h6083
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6084 | h6084
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6085 | h6085
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6086 | h6086
                        · linarith only [h0, h6074, h6078, h6086, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · linarith only [h0, h6074, h6077, h6078, h6086, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · linarith only [h0, h6074, h6077, h6078, h6085, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h6074, h6077, h6078, h6084, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · linarith only [h4130, h6077, h6083, hlam]
                · linarith only [h3260, h6076, h6082, hlam]
              · linarith only [h0, h6075, h6081, hlam]
            · linarith only [h0, h6074, h6080, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6095 | h6095
          · linarith only [h4558, h6074, h6095, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6097 | h6097
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6098 | h6098
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6099 | h6099
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6100 | h6100
                  · linarith only [h6076, h6077, h6095, h6097, h6100, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6102 | h6102
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6103 | h6103
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6104 | h6104
                        · linarith only [h4130, h6074, h6100, h6104, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6106 | h6106
                          · linarith only [h0, h4130, h6075, h6095, h6100, h6102, h6104, h6106, hc01, hc23, hlam, hphi, ht12]
                          · rcases h2bigk with h6108c | h6108c | h6108c | h6108c | h6108c | h6108c | h6108c | h6108c | h6108c | h6108c | h6108c | h6108c | h6108c | h6108c | h6108c | h6108c | h6108c | h6108c | h6108c | h6108c | h6108c | h6108c | h6108c | h6108c | h6108c
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [hlam, p6108_0]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [h0, hlam, p6108_0]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [h4558, hlam, p6108_0]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [h0, h6095, h6102, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6108_1, u4ehi3]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [h0, h6095, h6102, h6104, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6108_1, u4ehi3]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [h6095, hc02, hc23, hlam, hphi, p6108_1]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [hlam, p6108_0]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [h6095, hlam, p6108_0]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [h6095, h6102, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6108_1, u4ehi3]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [h6095, h6102, h6104, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6108_1, u4ehi3]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [h6075, h6102, h6104, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6108_1, u4ehi3]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p6108_1]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [hlam, p6108_0]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              rcases p6108_3 (m.d 0 2) (by simp) with h6122 | h6122
                              · linarith only [h4558, h6122, hlam]
                              · linarith only [h6074, h6122, hlam]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              rcases p6108_3 (m.d 0 2) (by simp) with h6125 | h6125
                              · linarith only [h4558, h6125, hlam]
                              · linarith only [h6075, h6125, hlam]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [h6074, hlam, p6108_0]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [h6097, hlam, p6108_0]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [h6102, hlam, p6108_0]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [hlam, p6108_0]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [h6104, hlam, p6108_0]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [h6075, hlam, p6108_0]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [h6098, hlam, p6108_0]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [h6103, hlam, p6108_0]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [h6075, h6102, hc02, hlam, hphi, ht0b, ht45, ht5b, p6108_1, u4ehi3]
                            · have p6108_0 := h6108c.1
                              have p6108_1 := h6108c.2.1
                              have p6108_2 := h6108c.2.2.1
                              have p6108_3 := h6108c.2.2.2
                              linarith only [hlam, p6108_0]
                      · linarith only [h0, h6095, h6103, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h6074, h6095, h6102, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · linarith only [h3260, h4558, h6074, h6076, h6099, hlam]
              · linarith only [h0, h6075, h6098, hlam]
            · linarith only [h0, h6074, h6097, hlam]
      · linarith only [h4558, h6074, h6076, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h6144 | h6144
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6145 | h6145
        · linarith only [h6074, h6075, h6145, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6147 | h6147
          · linarith only [h4558, h6074, h6147, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6149 | h6149
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6150 | h6150
              · linarith only [h6074, h6075, h6150, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6152 | h6152
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6153 | h6153
                  · linarith only [h6145, h6147, h6149, h6153, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6155 | h6155
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6156 | h6156
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6157 | h6157
                        · linarith only [h6074, h6153, h6157, hc02, hlam, hphi, ht0b, ht45, ht5b, u4ehi1]
                        · linarith only [h0, h6074, h6150, h6157, hc45, hlam, hphi, u4ehi2]
                      · linarith only [h4558, h6074, h6155, h6156, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h6074, h6147, h6155, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · linarith only [h3260, h6144, h6152, hlam]
            · linarith only [h0, h6074, h6149, hlam]
      · linarith only [h4558, h6074, h6144, hlam]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h6165 | h6165
    · rcases m.htr 0 3 4 (by decide) (by decide) with h6166 | h6166
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6167 | h6167
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6168 | h6168
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6169 | h6169
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6170 | h6170
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6171 | h6171
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6172 | h6172
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6173 | h6173
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6174 | h6174
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6175 | h6175
                        · linarith only [h6074, h6165, h6168, h6173, h6175, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                        · linarith only [h6074, h6165, h6166, h6167, h6175, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h6074, h6165, h6173, h6174, hlam]
                    · linarith only [h4558, h6166, h6173, hlam]
                  · linarith only [h4130, h6074, h6165, h6167, h6172, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h3260, h4558, h6166, h6168, h6171, hc01, hc12, hlam, hphi]
              · linarith only [h4558, h6165, h6168, h6170, hlam]
            · linarith only [h4558, h6168, h6169, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6184 | h6184
            · linarith only [h6074, h6165, h6167, h6168, h6184, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6186 | h6186
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6187 | h6187
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6188 | h6188
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6189 | h6189
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6190 | h6190
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6191 | h6191
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6192 | h6192
                          · rcases h2bigk with h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c | h6193c
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [hlam, p6193_0]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [h0, hlam, p6193_0]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [h4558, hlam, p6193_0]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [h6074, hlam, p6193_0]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [h0, h6184, h6189, h6190, h6192, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6193_1, u4ehi4]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [h6184, h6189, hc02, hc23, hlam, hphi, p6193_1]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [hlam, p6193_0]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [h6168, hlam, p6193_0]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [h6184, hlam, p6193_0]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [h6184, h6189, h6190, h6192, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6193_1, u4ehi4]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [h6165, h6190, h6192, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6193_1, u4ehi4]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p6193_1]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [hlam, p6193_0]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [h6074, h6165, h6190, h6192, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6193_1, u4ehi4]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              rcases p6193_3 (m.d 0 2) (by simp) with h6208 | h6208
                              · linarith only [h4558, h6208, hlam]
                              · linarith only [h6165, h6208, hlam]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [h6165, h6190, h6192, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6193_1, u4ehi4]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [h0, h6165, h6190, h6192, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6193_1, u4ehi4]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [h6189, hlam, p6193_0]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [hlam, p6193_0]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              rcases p6193_3 (m.d 0 2) (by simp) with h6215 | h6215
                              · linarith only [h6074, h6215, hlam]
                              · linarith only [h6165, h6215, hlam]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [h6165, hlam, p6193_0]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [h6186, hlam, p6193_0]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [h6190, hlam, p6193_0]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [h6191, hlam, p6193_1]
                            · have p6193_0 := h6193c.1
                              have p6193_1 := h6193c.2.1
                              have p6193_2 := h6193c.2.2.1
                              have p6193_3 := h6193c.2.2.2
                              linarith only [hlam, p6193_0]
                          · linarith only [h0, h6165, h6184, h6189, h6191, h6192, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                        · linarith only [h0, h6184, h6191, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h6184, h6189, h6190, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h3260, h6166, h6168, h6189, hlam]
                  · linarith only [h0, h4130, h6165, h6167, h6168, h6188, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h3260, h6166, h6187, hlam]
              · linarith only [h0, h6165, h6186, hlam]
        · linarith only [h6074, h6165, h6167, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6231 | h6231
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6232 | h6232
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6233 | h6233
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6234 | h6234
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6235 | h6235
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6236 | h6236
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6237 | h6237
                    · linarith only [h4558, h6165, h6166, h6231, h6232, h6237, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h4558, h6165, h6231, h6235, h6237, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h4130, h4558, h6165, h6231, h6236, hc01, hc23, hlam, hphi, ht12]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6241 | h6241
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6242 | h6242
                    · linarith only [h6232, h6235, h6242, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6244 | h6244
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6245 | h6245
                        · linarith only [h4558, h6165, h6232, h6235, h6245, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                        · linarith only [h4558, h6165, h6231, h6242, h6245, hc04, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h4558, h6165, h6244, hlam]
                  · linarith only [h4558, h6165, h6231, h6232, h6235, h6241, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
              · linarith only [h6074, h6165, h6233, h6234, hlam]
            · linarith only [h4558, h6232, h6233, hc02, hc24, hlam, hphi]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6252 | h6252
            · linarith only [h6074, h6165, h6231, h6232, h6252, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6254 | h6254
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6255 | h6255
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6256 | h6256
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6257 | h6257
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6258 | h6258
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6259 | h6259
                        · linarith only [h4558, h6165, h6166, h6232, h6255, h6259, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                        · linarith only [h4359, h6252, h6254, h6259, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h4558, h6165, h6166, h6231, h6232, h6255, h6258, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                    · linarith only [h6232, h6255, h6257, hlam]
                  · linarith only [h4558, h6165, h6166, h6231, h6255, h6256, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6265 | h6265
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6266 | h6266
                    · linarith only [h4359, h6232, h6254, h6255, h6266, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h4359, h6232, h6254, h6266, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h4130, h6165, h6231, h6232, h6265, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h4558, h6165, h6166, h6254, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h4558, h6165, h6166, h6231, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h6272 | h6272
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6273 | h6273
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6274 | h6274
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6275 | h6275
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6276 | h6276
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6277 | h6277
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6278 | h6278
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6279 | h6279
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6280 | h6280
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6281 | h6281
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6282 | h6282
                          · linarith only [h4558, h6272, h6274, h6282, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                          · linarith only [h4558, h6272, h6273, h6274, h6282, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h4558, h6272, h6273, h6274, h6281, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6286 | h6286
                        · linarith only [h6279, h6280, h6286, hlam]
                        · linarith only [h4558, h6074, h6272, h6273, h6280, h6286, hc02, hc35, hlam, hphi, ht23]
                    · linarith only [h4558, h6272, h6279, hlam]
                  · linarith only [h4130, h4558, h6272, h6273, h6278, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h4558, h6272, h6274, h6277, hlam]
              · linarith only [h4558, h6272, h6274, h6276, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · linarith only [h4558, h6272, h6273, h6274, h6275, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6294 | h6294
            · linarith only [h0, h6074, h6274, h6294, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6296 | h6296
              · linarith only [h0, h6165, h6274, h6296, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6298 | h6298
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6299 | h6299
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6300 | h6300
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6301 | h6301
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6302 | h6302
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6303 | h6303
                          · rcases h2bigk with h6304c | h6304c | h6304c | h6304c | h6304c | h6304c | h6304c | h6304c | h6304c | h6304c | h6304c | h6304c | h6304c | h6304c | h6304c | h6304c | h6304c | h6304c | h6304c | h6304c | h6304c | h6304c | h6304c | h6304c | h6304c
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [hlam, p6304_0]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [h0, hlam, p6304_0]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [h4558, hlam, p6304_0]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [h6074, hlam, p6304_0]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [h6165, hlam, p6304_0]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [h0, h6296, h6300, h6302, hc01, hc23, hlam, hphi, ht12, p6304_1]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [hlam, p6304_0]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [h6274, hlam, p6304_0]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [h6294, hlam, p6304_0]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [h6296, hlam, p6304_0]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              rcases p6304_3 (m.d 0 2) (by simp) with h6315 | h6315
                              · linarith only [h6315, hlam, p6304_0]
                              · rcases p6304_3 (m.d 1 2) (by simp) with h6317 | h6317
                                · linarith only [h6274, h6317, hlam]
                                · linarith only [h0, h6317, hlam]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p6304_1]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [hlam, p6304_0]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [h0, h6074, hc01, hc23, hlam, hphi, ht12, p6304_1]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [h0, h6296, hc01, hc23, hlam, hphi, ht12, p6304_1]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              rcases p6304_3 (m.d 0 2) (by simp) with h6324 | h6324
                              · linarith only [h6324, hlam, p6304_0]
                              · rcases p6304_3 (m.d 1 2) (by simp) with h6326 | h6326
                                · linarith only [h6294, h6326, hlam]
                                · linarith only [h0, h6326, hlam]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p6304_1]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [h6300, hlam, p6304_0]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [hlam, p6304_0]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [h0, h6296, h6300, hc01, hc23, hlam, hphi, ht12, p6304_1]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              rcases p6304_3 (m.d 0 2) (by simp) with h6333 | h6333
                              · linarith only [h6333, hlam, p6304_0]
                              · rcases p6304_3 (m.d 1 2) (by simp) with h6335 | h6335
                                · linarith only [h6296, h6335, hlam]
                                · linarith only [h0, h6335, hlam]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p6304_1]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [h6301, hlam, p6304_0]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [h6302, hlam, p6304_1]
                            · have p6304_0 := h6304c.1
                              have p6304_1 := h6304c.2.1
                              have p6304_2 := h6304c.2.2.1
                              have p6304_3 := h6304c.2.2.2
                              linarith only [hlam, p6304_0]
                          · rcases h2bigk with h6342c | h6342c | h6342c | h6342c | h6342c | h6342c | h6342c | h6342c | h6342c | h6342c | h6342c | h6342c | h6342c | h6342c | h6342c | h6342c | h6342c | h6342c | h6342c | h6342c | h6342c | h6342c | h6342c | h6342c | h6342c
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [hlam, p6342_0]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [h0, hlam, p6342_0]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [h4558, hlam, p6342_0]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [h6074, hlam, p6342_0]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [h6165, hlam, p6342_0]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [h0, h6274, hc01, hc23, hlam, hphi, ht12, p6342_1]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [hlam, p6342_0]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [h6274, hlam, p6342_0]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [h6294, hlam, p6342_0]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [h6296, hlam, p6342_0]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              rcases p6342_3 (m.d 0 2) (by simp) with h6353 | h6353
                              · linarith only [h6353, hlam, p6342_0]
                              · rcases p6342_3 (m.d 1 2) (by simp) with h6355 | h6355
                                · linarith only [h6274, h6355, hlam]
                                · linarith only [h0, h6355, hlam]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p6342_1]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [hlam, p6342_0]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [h0, h6074, hc01, hc23, hlam, hphi, ht12, p6342_1]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [h0, h6165, hc01, hc23, hlam, hphi, ht12, p6342_1]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              rcases p6342_3 (m.d 0 2) (by simp) with h6362 | h6362
                              · linarith only [h6362, hlam, p6342_0]
                              · rcases p6342_3 (m.d 1 2) (by simp) with h6364 | h6364
                                · linarith only [h6294, h6364, hlam]
                                · linarith only [h0, h6364, hlam]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p6342_1]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [h6300, hlam, p6342_0]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [hlam, p6342_0]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [h0, h6296, h6300, hc01, hc23, hlam, hphi, ht12, p6342_1]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              rcases p6342_3 (m.d 0 2) (by simp) with h6371 | h6371
                              · linarith only [h6371, hlam, p6342_0]
                              · rcases p6342_3 (m.d 1 2) (by simp) with h6373 | h6373
                                · linarith only [h6296, h6373, hlam]
                                · linarith only [h0, h6373, hlam]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p6342_1]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [h6301, hlam, p6342_0]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [h6302, hlam, p6342_1]
                            · have p6342_0 := h6342c.1
                              have p6342_1 := h6342c.2.1
                              have p6342_2 := h6342c.2.2.1
                              have p6342_3 := h6342c.2.2.2
                              linarith only [hlam, p6342_0]
                        · linarith only [h0, h3260, h6074, h6272, h6273, h6302, hc01, hc13, hlam, hphi]
                      · linarith only [h0, h6274, h6301, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h6274, h6300, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h4130, h6273, h6299, hlam]
                · linarith only [h3260, h6272, h6298, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6385 | h6385
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6386 | h6386
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6387 | h6387
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6388 | h6388
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6389 | h6389
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6390 | h6390
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6391 | h6391
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6392 | h6392
                        · linarith only [h6272, h6273, h6386, h6392, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h0, h6074, h6389, h6392, hc01, hc14, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6395 | h6395
                        · linarith only [h6272, h6273, h6386, h6395, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                        · linarith only [h0, h6074, h6385, h6388, h6389, h6395, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h3260, h4558, h6272, h6385, h6390, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6399 | h6399
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6400 | h6400
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6401 | h6401
                        · linarith only [h6386, h6389, h6401, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6403 | h6403
                          · linarith only [h4558, h6074, h6272, h6385, h6386, h6389, h6403, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                          · rcases h2bigk with h6405c | h6405c | h6405c | h6405c | h6405c | h6405c | h6405c | h6405c | h6405c | h6405c | h6405c | h6405c | h6405c | h6405c | h6405c | h6405c | h6405c | h6405c | h6405c | h6405c | h6405c | h6405c | h6405c | h6405c | h6405c
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [hlam, p6405_0]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [h0, hlam, p6405_0]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [h4558, hlam, p6405_0]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [h6074, hlam, p6405_0]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [h6165, hlam, p6405_0]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              rcases p6405_3 (m.d 0 2) (by simp) with h6411 | h6411
                              · linarith only [h0, h6411, hlam]
                              · rcases p6405_3 (m.d 1 2) (by simp) with h6413 | h6413
                                · rcases p6405_3 (m.d 2 3) (by simp) with h6414 | h6414
                                  · linarith only [h6385, h6414, hlam]
                                  · linarith only [h4558, h6414, hlam]
                                · linarith only [h0, h6413, hlam]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [hlam, p6405_0]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [h0, h4558, hc01, hc12, hlam, hphi, p6405_1]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [h0, h6074, hc01, hc12, hlam, hphi, p6405_1]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [h0, h6074, h6401, hc01, hc12, hlam, hphi, p6405_1]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [h0, h6385, hc01, hc12, hlam, hphi, p6405_1]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [h6385, hlam, p6405_0]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [hlam, p6405_0]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [h0, h6074, h6385, hc01, hc12, hlam, hphi, p6405_1]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [h0, h6074, h6385, h6401, hc01, hc12, hlam, hphi, p6405_1]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [h0, h6386, h6389, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p6405_1]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [h6386, hlam, p6405_0]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [h6399, hlam, p6405_0]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [hlam, p6405_0]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [h6401, hlam, p6405_0]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [h0, h6387, hc01, hc12, hlam, hphi, p6405_1]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [h6387, hlam, p6405_0]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [h6400, hlam, p6405_0]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [h6385, h6400, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6405_1, u4ehi2]
                            · have p6405_0 := h6405c.1
                              have p6405_1 := h6405c.2.1
                              have p6405_2 := h6405c.2.2.1
                              have p6405_3 := h6405c.2.2.2
                              linarith only [hlam, p6405_0]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6437 | h6437
                        · linarith only [h4130, h6389, h6437, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6439 | h6439
                          · linarith only [h0, h6074, h6272, h6386, h6389, h6439, hc01, hc03, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                          · linarith only [h4558, h6272, h6400, h6439, hc45, hlam, hphi, u4ehi3]
                    · linarith only [h4558, h6272, h6399, hlam]
                · linarith only [h3260, h4558, h6272, h6388, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h4558, h6272, h6385, h6387, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · linarith only [h4558, h6272, h6385, h6386, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6446 | h6446
            · linarith only [h0, h6074, h6385, h6446, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6448 | h6448
              · linarith only [h0, h6165, h6385, h6448, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6450 | h6450
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6451 | h6451
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6452 | h6452
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6453 | h6453
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6454 | h6454
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6455 | h6455
                          · linarith only [h6272, h6273, h6455, hlam]
                          · rcases h2bigk with h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c | h6457c
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [hlam, p6457_0]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [h0, hlam, p6457_0]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [h4558, hlam, p6457_0]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [h6074, hlam, p6457_0]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [h6165, hlam, p6457_0]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [h0, h6448, h6452, h6454, hc01, hc23, hlam, hphi, ht12, p6457_1]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [hlam, p6457_0]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [h6385, hlam, p6457_0]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [h6446, hlam, p6457_0]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [h6448, hlam, p6457_0]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              rcases p6457_3 (m.d 0 2) (by simp) with h6468 | h6468
                              · linarith only [h6468, hlam, p6457_0]
                              · rcases p6457_3 (m.d 1 2) (by simp) with h6470 | h6470
                                · linarith only [h6385, h6470, hlam]
                                · linarith only [h0, h6470, hlam]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p6457_1]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [hlam, p6457_0]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [h0, h6074, hc01, hc23, hlam, hphi, ht12, p6457_1]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [h0, h6448, hc01, hc23, hlam, hphi, ht12, p6457_1]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              rcases p6457_3 (m.d 0 2) (by simp) with h6477 | h6477
                              · linarith only [h6477, hlam, p6457_0]
                              · rcases p6457_3 (m.d 1 2) (by simp) with h6479 | h6479
                                · linarith only [h6446, h6479, hlam]
                                · linarith only [h0, h6479, hlam]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p6457_1]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [h6452, hlam, p6457_0]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [hlam, p6457_0]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [h0, h6448, h6452, hc01, hc23, hlam, hphi, ht12, p6457_1]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              rcases p6457_3 (m.d 0 2) (by simp) with h6486 | h6486
                              · linarith only [h6486, hlam, p6457_0]
                              · rcases p6457_3 (m.d 1 2) (by simp) with h6488 | h6488
                                · linarith only [h6448, h6488, hlam]
                                · linarith only [h0, h6488, hlam]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p6457_1]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [h6453, hlam, p6457_0]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [h6454, hlam, p6457_1]
                            · have p6457_0 := h6457c.1
                              have p6457_1 := h6457c.2.1
                              have p6457_2 := h6457c.2.2.1
                              have p6457_3 := h6457c.2.2.2
                              linarith only [hlam, p6457_0]
                        · linarith only [h0, h6074, h6450, h6451, h6454, hc01, hc13, hlam, hphi]
                      · linarith only [h6272, h6273, h6385, h6450, h6451, h6453, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                    · linarith only [h6272, h6273, h6385, h6450, h6451, h6452, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6498 | h6498
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6499 | h6499
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6500 | h6500
                        · linarith only [h4130, h6451, h6500, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h0, h6446, h6500, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h6385, h6499, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h3260, h6272, h6385, h6498, hlam]
                · linarith only [h3260, h6272, h6450, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6506 | h6506
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6507 | h6507
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6508 | h6508
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6509 | h6509
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6510 | h6510
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6511 | h6511
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6512 | h6512
                    · linarith only [h3260, h6272, h6507, h6512, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h4558, h6507, h6510, h6512, hc01, hc12, hlam, hphi]
                  · linarith only [h6272, h6506, h6507, h6510, h6511, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6516 | h6516
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6517 | h6517
                    · linarith only [h6507, h6510, h6517, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6519 | h6519
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6520 | h6520
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6521 | h6521
                          · rcases h2bigk with h6522c | h6522c | h6522c | h6522c | h6522c | h6522c | h6522c | h6522c | h6522c | h6522c | h6522c | h6522c | h6522c | h6522c | h6522c | h6522c | h6522c | h6522c | h6522c | h6522c | h6522c | h6522c | h6522c | h6522c | h6522c
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [hlam, p6522_0]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [h0, hlam, p6522_0]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [h4558, hlam, p6522_0]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [h6074, hlam, p6522_0]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [h6165, hlam, p6522_0]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              rcases p6522_3 (m.d 0 2) (by simp) with h6528 | h6528
                              · linarith only [h0, h6528, hlam]
                              · rcases p6522_3 (m.d 1 2) (by simp) with h6530 | h6530
                                · rcases p6522_3 (m.d 2 3) (by simp) with h6531 | h6531
                                  · linarith only [h6507, h6531, hlam]
                                  · linarith only [h4558, h6531, hlam]
                                · linarith only [h0, h6530, hlam]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [hlam, p6522_0]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [h6519, h6521, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6522_1, u4ehi4]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [h0, h6074, hc01, hc12, hlam, hphi, p6522_1]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [h0, h6165, hc01, hc12, hlam, hphi, p6522_1]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [h0, h6507, h6510, hc01, hc34, hlam, hphi, ht12, ht23, p6522_1]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [h6507, hlam, p6522_0]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [hlam, p6522_0]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [h6517, hlam, p6522_1]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [h0, h6165, h6507, h6510, hc01, hc34, hlam, hphi, ht12, ht23, p6522_1]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [h0, h6508, hc01, hc12, hlam, hphi, p6522_1]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [h6508, hlam, p6522_0]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [h0, h4558, h6508, hc01, hc12, hlam, hphi, p6522_1]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [hlam, p6522_0]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [h0, h6165, h6508, hc01, hc12, hlam, hphi, p6522_1]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [h0, h6509, hc01, hc12, hlam, hphi, p6522_1]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [h6509, hlam, p6522_0]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [h6519, hlam, p6522_0]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [h6520, hlam, p6522_1]
                            · have p6522_0 := h6522c.1
                              have p6522_1 := h6522c.2.1
                              have p6522_2 := h6522c.2.2.1
                              have p6522_3 := h6522c.2.2.2
                              linarith only [hlam, p6522_0]
                          · linarith only [h6506, h6507, h6510, h6519, h6521, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h6074, h6506, h6520, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6556 | h6556
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6557 | h6557
                          · rcases h2bigk with h6558c | h6558c | h6558c | h6558c | h6558c | h6558c | h6558c | h6558c | h6558c | h6558c | h6558c | h6558c | h6558c | h6558c | h6558c | h6558c | h6558c | h6558c | h6558c | h6558c | h6558c | h6558c | h6558c | h6558c | h6558c
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [hlam, p6558_0]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [h0, hlam, p6558_0]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [h4558, hlam, p6558_0]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [h6074, hlam, p6558_0]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [h6165, hlam, p6558_0]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              rcases p6558_3 (m.d 0 2) (by simp) with h6564 | h6564
                              · linarith only [h0, h6564, hlam]
                              · rcases p6558_3 (m.d 1 2) (by simp) with h6566 | h6566
                                · rcases p6558_3 (m.d 2 3) (by simp) with h6567 | h6567
                                  · linarith only [h6507, h6567, hlam]
                                  · linarith only [h4558, h6567, hlam]
                                · linarith only [h0, h6566, hlam]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [hlam, p6558_0]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [h0, h4558, hc01, hc12, hlam, hphi, p6558_1]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [h6074, h6506, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p6558_1, u4ehi4]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [h0, h4558, h6519, hc01, hc12, hlam, hphi, p6558_1]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [h0, h6519, hc01, hc35, hlam, hphi, ht12, ht23, p6558_1]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [h6507, hlam, p6558_0]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [hlam, p6558_0]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [h6517, hlam, p6558_1]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [h6519, hlam, p6558_1]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [h0, h6508, hc01, hc12, hlam, hphi, p6558_1]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [h6508, hlam, p6558_0]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [h0, h4558, h6508, hc01, hc12, hlam, hphi, p6558_1]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [hlam, p6558_0]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [h0, h4558, h6508, h6519, hc01, hc12, hlam, hphi, p6558_1]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [h0, h6509, hc01, hc12, hlam, hphi, p6558_1]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [h6509, hlam, p6558_0]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [h0, h4558, h6509, hc01, hc12, hlam, hphi, p6558_1]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [h6556, hlam, p6558_1]
                            · have p6558_0 := h6558c.1
                              have p6558_1 := h6558c.2.1
                              have p6558_2 := h6558c.2.2.1
                              have p6558_3 := h6558c.2.2.2
                              linarith only [hlam, p6558_0]
                          · linarith only [h3260, h6506, h6510, h6557, hc01, hc04, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · linarith only [h6074, h6506, h6556, hlam]
                  · linarith only [h6074, h6506, h6508, h6516, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
              · linarith only [h6074, h6506, h6508, h6509, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · linarith only [h0, h4558, h6507, h6508, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6595 | h6595
            · linarith only [h6074, h6506, h6507, h6595, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6597 | h6597
              · linarith only [h0, h6165, h6507, h6597, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6599 | h6599
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6600 | h6600
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6601 | h6601
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6602 | h6602
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6603 | h6603
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6604 | h6604
                          · rcases h2bigk with h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c | h6605c
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [hlam, p6605_0]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [h0, hlam, p6605_0]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [h4558, hlam, p6605_0]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [h6074, hlam, p6605_0]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [h6165, hlam, p6605_0]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [h0, h6597, h6601, h6603, hc01, hc23, hlam, hphi, ht12, p6605_1]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [hlam, p6605_0]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [h6507, hlam, p6605_0]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [h6595, hlam, p6605_0]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [h6597, hlam, p6605_0]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              rcases p6605_3 (m.d 0 2) (by simp) with h6616 | h6616
                              · linarith only [h6616, hlam, p6605_0]
                              · rcases p6605_3 (m.d 1 2) (by simp) with h6618 | h6618
                                · linarith only [h6507, h6618, hlam]
                                · linarith only [h0, h6618, hlam]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [h0, hc01, hc23, hlam, hphi, ht12, p6605_1]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [hlam, p6605_0]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [h0, h6074, hc01, hc23, hlam, hphi, ht12, p6605_1]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [h0, h6597, hc01, hc23, hlam, hphi, ht12, p6605_1]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              rcases p6605_3 (m.d 0 2) (by simp) with h6625 | h6625
                              · linarith only [h6625, hlam, p6605_0]
                              · rcases p6605_3 (m.d 1 2) (by simp) with h6627 | h6627
                                · linarith only [h6595, h6627, hlam]
                                · linarith only [h0, h6627, hlam]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [h0, hc01, hc24, hlam, hphi, ht12, p6605_1]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [h6601, hlam, p6605_0]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [hlam, p6605_0]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [h0, h6597, h6601, hc01, hc23, hlam, hphi, ht12, p6605_1]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              rcases p6605_3 (m.d 0 2) (by simp) with h6634 | h6634
                              · linarith only [h6634, hlam, p6605_0]
                              · rcases p6605_3 (m.d 1 2) (by simp) with h6636 | h6636
                                · linarith only [h6597, h6636, hlam]
                                · linarith only [h0, h6636, hlam]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht12, p6605_1]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [h6602, hlam, p6605_0]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [h6603, hlam, p6605_1]
                            · have p6605_0 := h6605c.1
                              have p6605_1 := h6605c.2.1
                              have p6605_2 := h6605c.2.2.1
                              have p6605_3 := h6605c.2.2.2
                              linarith only [hlam, p6605_0]
                          · linarith only [h3260, h4130, h6272, h6506, h6604, hc01, hc14, hlam, hphi]
                        · linarith only [h6272, h6506, h6599, h6603, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h6272, h6507, h6599, h6602, hc03, hc35, hlam, hphi]
                    · linarith only [h6507, h6599, h6601, hlam]
                  · linarith only [h6272, h6506, h6599, h6600, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6648 | h6648
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6649 | h6649
                    · linarith only [h3260, h6599, h6649, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h6507, h6649, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h4130, h6506, h6648, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6653 | h6653
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6654 | h6654
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6655 | h6655
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6656 | h6656
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6657 | h6657
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6658 | h6658
                    · linarith only [h0, h4558, h6272, h6653, h6658, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h4558, h6653, h6656, h6658, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6661 | h6661
                    · linarith only [h0, h4558, h6272, h6653, h6661, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h4558, h6656, h6657, h6661, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6664 | h6664
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6665 | h6665
                    · linarith only [h3260, h6656, h6665, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6667 | h6667
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6668 | h6668
                        · linarith only [h6506, h6654, h6668, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                        · linarith only [h0, h6074, h6664, h6668, hc01, hc14, hlam, hphi]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6671 | h6671
                        · linarith only [h6506, h6654, h6671, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi0]
                        · linarith only [h0, h6074, h6656, h6664, h6671, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6674 | h6674
                    · linarith only [h0, h4558, h6272, h6653, h6674, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6676 | h6676
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6677 | h6677
                        · linarith only [h3260, h6656, h6664, h6677, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h6674, h6676, h6677, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6680 | h6680
                        · linarith only [h3260, h6656, h6664, h6680, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6682 | h6682
                          · linarith only [h4558, h6653, h6656, h6664, h6682, hc02, hc34, hlam, hphi, ht23]
                          · linarith only [h0, h4558, h6653, h6656, h6682, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
              · linarith only [h0, h4558, h6653, h6655, hc01, hc25, hlam, hphi, ht12]
            · linarith only [h0, h4558, h6653, h6654, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6687 | h6687
            · linarith only [h0, h6074, h6653, h6687, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6689 | h6689
              · linarith only [h0, h6165, h6653, h6689, hc01, hc23, hlam, hphi, ht12]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6691 | h6691
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6692 | h6692
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6693 | h6693
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6694 | h6694
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6695 | h6695
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6696 | h6696
                          · linarith only [h6506, h6653, h6691, h6696, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                          · linarith only [h0, h4558, h6272, h6653, h6691, h6692, h6696, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h0, h6074, h6653, h6691, h6692, h6695, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h6506, h6653, h6691, h6692, h6694, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                    · linarith only [h6506, h6653, h6691, h6692, h6693, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6702 | h6702
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6703 | h6703
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6704 | h6704
                        · linarith only [h0, h4558, h6272, h6691, h6692, h6704, hc01, hc24, hlam, hphi, ht12]
                        · linarith only [h0, h6687, h6704, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h0, h6653, h6703, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h6653, h6691, h6702, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6709 | h6709
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6710 | h6710
                    · linarith only [h6506, h6691, h6709, h6710, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                    · linarith only [h0, h6653, h6710, hc01, hc34, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6713 | h6713
                    · linarith only [h3260, h6691, h6713, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h0, h6653, h6713, hc01, hc34, hlam, hphi, ht12, ht23]

set_option maxHeartbeats 5172000 in
set_option maxHeartbeats 5172000 in
theorem r1l7_12_24_L_I_M_IR_s3_x1_x1 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_M_IR m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg3260 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h4130 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h4359 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h2bigk := hb2.1
  have h4ehi := hb4.2.1
  have h4bigk := hb4.2.2.2
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h3260 := hg3260
  rcases m.htr 0 2 3 (by decide) (by decide) with h4558 | h4558
  · exact r1l7_12_24_L_I_M_IR_s3_x1_x1_x0 m hb2 hb4 hg0 hg3260 h4130 h4359 h4558
  · exact r1l7_12_24_L_I_M_IR_s3_x1_x1_x1 m hb2 hb4 hg0 hg3260 h4130 h4359 h4558

end R2N4
