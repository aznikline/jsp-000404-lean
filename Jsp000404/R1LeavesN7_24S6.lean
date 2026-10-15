import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_24S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5514000 in
set_option maxHeartbeats 5514000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3363 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h3364 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3365 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3366 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3367 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3368 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h3369 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 5 (by decide) (by decide) with h3828 | h3828
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3829 | h3829
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3830 | h3830
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3831 | h3831
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3832 | h3832
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3833 | h3833
            · linarith only [h0, h3363, h3369, h3833, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3835 | h3835
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3836 | h3836
                · linarith only [h3363, h3369, h3830, h3836, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3838 | h3838
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3839 | h3839
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3840 | h3840
                      · rcases h0bigk with h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c | h3841c
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [hlam, p3841_0]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [h0, hlam, p3841_1]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [h0, h3363, h3830, h3838, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3841_1]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [h0, h3363, h3369, h3830, h3838, h3840, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3841_1]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          rcases p3841_3 (m.d 0 1) (by simp) with h3846 | h3846
                          · rcases p3841_3 (m.d 0 2) (by simp) with h3847 | h3847
                            · rcases p3841_3 (m.d 0 3) (by simp) with h3848 | h3848
                              · linarith only [h3363, h3848, hlam]
                              · linarith only [h3828, h3848, hlam]
                            · linarith only [h3368, h3847, hlam]
                          · linarith only [h3365, h3846, hlam]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [h0, h3363, h3830, h3838, h3840, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3841_1]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [hlam, p3841_0]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          rcases p3841_3 (m.d 0 1) (by simp) with h3855 | h3855
                          · linarith only [h0, h3855, hlam]
                          · linarith only [h3363, h3855, hlam]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          rcases p3841_3 (m.d 0 1) (by simp) with h3858 | h3858
                          · linarith only [h0, h3858, hlam]
                          · linarith only [h3364, h3858, hlam]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          rcases p3841_3 (m.d 0 1) (by simp) with h3861 | h3861
                          · linarith only [h0, h3861, hlam]
                          · linarith only [h3365, h3861, hlam]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [h3363, hlam, p3841_1]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [h3366, hlam, p3841_1]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [hlam, p3841_0]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [h3369, hlam, p3841_1]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [h3365, h3369, h3832, h3838, h3840, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3841_1, u3elo3]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [h3364, hlam, p3841_0]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [h3367, hlam, p3841_0]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [h0, h3363, h3364, h3830, h3838, h3840, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3841_1]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [hlam, p3841_0]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          rcases p3841_3 (m.d 0 1) (by simp) with h3873 | h3873
                          · rcases p3841_3 (m.d 0 2) (by simp) with h3874 | h3874
                            · rcases p3841_3 (m.d 0 3) (by simp) with h3875 | h3875
                              · linarith only [h3369, h3875, hlam]
                              · linarith only [h3828, h3875, hlam]
                            · linarith only [h3368, h3874, hlam]
                          · linarith only [h3365, h3873, hlam]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [h3365, hlam, p3841_0]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [h3368, hlam, p3841_1]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [h3828, hlam, p3841_0]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [h3829, hlam, p3841_1]
                        · have p3841_0 := h3841c.1
                          have p3841_1 := h3841c.2.1
                          have p3841_2 := h3841c.2.2.1
                          have p3841_3 := h3841c.2.2.2
                          linarith only [hlam, p3841_0]
                      · linarith only [h3363, h3369, h3829, h3830, h3838, h3840, hc04, hc35, hlam, hphi, ht0b, ht5b]
                    · linarith only [h3369, h3828, h3829, h3836, h3838, h3839, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                  · linarith only [h3369, h3828, h3838, hc23, hlam, hphi, u3elo3]
              · linarith only [h3369, h3828, h3835, hc13, hlam, hphi, u3elo3]
          · linarith only [h0, h3368, h3832, hlam]
        · linarith only [h0, h3367, h3831, hlam]
      · linarith only [h0, h3830, hc01, hlam, hphi, ht12, ht23, u3elo2]
    · linarith only [h3369, h3828, h3829, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h3893 | h3893
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3894 | h3894
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3895 | h3895
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3896 | h3896
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3897 | h3897
            · linarith only [h0, h3363, h3369, h3897, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3899 | h3899
              · linarith only [h3363, h3828, h3899, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3901 | h3901
                · linarith only [h3366, h3369, h3901, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3903 | h3903
                  · linarith only [h3828, h3894, h3903, hc03, hlam, hphi, u3elo1]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3905 | h3905
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3906 | h3906
                      · rcases h0bigk with h3907c | h3907c | h3907c | h3907c | h3907c | h3907c | h3907c | h3907c | h3907c | h3907c | h3907c | h3907c | h3907c | h3907c | h3907c | h3907c | h3907c | h3907c | h3907c | h3907c | h3907c | h3907c | h3907c | h3907c | h3907c
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [hlam, p3907_0]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [h0, hlam, p3907_1]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          rcases p3907_3 (m.d 0 1) (by simp) with h3910 | h3910
                          · rcases p3907_3 (m.d 0 2) (by simp) with h3911 | h3911
                            · rcases p3907_3 (m.d 0 3) (by simp) with h3912 | h3912
                              · linarith only [h3363, h3912, hlam]
                              · rcases p3907_3 (m.d 0 4) (by simp) with h3914 | h3914
                                · linarith only [h3364, h3914, hlam]
                                · linarith only [h3369, h3914, hlam]
                            · linarith only [h3366, h3911, hlam]
                          · linarith only [h3363, h3910, hlam]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [h0, h3364, h3895, h3905, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3907_1]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          rcases p3907_3 (m.d 0 1) (by simp) with h3920 | h3920
                          · rcases p3907_3 (m.d 0 2) (by simp) with h3921 | h3921
                            · rcases p3907_3 (m.d 0 3) (by simp) with h3922 | h3922
                              · linarith only [h3363, h3922, hlam]
                              · rcases p3907_3 (m.d 0 4) (by simp) with h3924 | h3924
                                · linarith only [h3364, h3924, hlam]
                                · linarith only [h3893, h3924, hlam]
                            · linarith only [h3368, h3921, hlam]
                          · linarith only [h3365, h3920, hlam]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [h0, h3364, h3895, h3905, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3907_1]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [hlam, p3907_0]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          rcases p3907_3 (m.d 0 1) (by simp) with h3931 | h3931
                          · linarith only [h0, h3931, hlam]
                          · linarith only [h3363, h3931, hlam]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          rcases p3907_3 (m.d 0 1) (by simp) with h3934 | h3934
                          · linarith only [h0, h3934, hlam]
                          · linarith only [h3364, h3934, hlam]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          rcases p3907_3 (m.d 0 1) (by simp) with h3937 | h3937
                          · linarith only [h0, h3937, hlam]
                          · linarith only [h3365, h3937, hlam]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [h3363, hlam, p3907_1]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [h3366, hlam, p3907_1]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [hlam, p3907_0]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [h3369, hlam, p3907_1]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [h3828, hlam, p3907_1]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [h3364, hlam, p3907_0]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [h3367, hlam, p3907_0]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [h3363, h3369, h3894, hc23, hlam, hphi, p3907_1, u3elo3]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [hlam, p3907_0]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [h3363, h3369, h3828, h3894, hc23, hlam, hphi, p3907_1, u3elo3]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [h3365, hlam, p3907_0]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [h3368, hlam, p3907_1]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [h3363, h3828, h3894, h3906, hc23, hlam, hphi, p3907_1, u3elo3]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [h3893, hlam, p3907_1]
                        · have p3907_0 := h3907c.1
                          have p3907_1 := h3907c.2.1
                          have p3907_2 := h3907c.2.2.1
                          have p3907_3 := h3907c.2.2.2
                          linarith only [hlam, p3907_0]
                      · linarith only [h0, h3364, h3369, h3895, h3905, h3906, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h3369, h3893, h3901, h3905, hc23, hlam, hphi, u3elo3]
          · linarith only [h0, h3368, h3896, hlam]
        · linarith only [h0, h3367, h3895, hlam]
      · linarith only [h0, h3894, hc01, hlam, hphi, ht12, ht23, u3elo2]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h3960 | h3960
      · rcases m.htr 1 2 4 (by decide) (by decide) with h3961 | h3961
        · rcases m.htr 1 2 5 (by decide) (by decide) with h3962 | h3962
          · rcases m.htr 1 3 4 (by decide) (by decide) with h3963 | h3963
            · linarith only [h3363, h3369, h3963, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h3965 | h3965
              · linarith only [h3363, h3828, h3965, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h3967 | h3967
                · linarith only [h3363, h3369, h3960, h3967, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h3969 | h3969
                  · linarith only [h3363, h3828, h3960, h3969, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h3971 | h3971
                    · linarith only [h3367, h3893, h3971, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h3973 | h3973
                      · linarith only [h3363, h3369, h3893, h3960, h3973, hc23, hlam, hphi, u3elo3]
                      · rcases h0bigk with h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c | h3975c
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          linarith only [hlam, p3975_0]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          linarith only [h0, hlam, p3975_1]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          rcases p3975_3 (m.d 0 1) (by simp) with h3978 | h3978
                          · rcases p3975_3 (m.d 0 2) (by simp) with h3979 | h3979
                            · rcases p3975_3 (m.d 0 3) (by simp) with h3980 | h3980
                              · linarith only [h3363, h3980, hlam]
                              · rcases p3975_3 (m.d 0 4) (by simp) with h3982 | h3982
                                · linarith only [h3364, h3982, hlam]
                                · linarith only [h3369, h3982, hlam]
                            · linarith only [h3366, h3979, hlam]
                          · linarith only [h3363, h3978, hlam]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          rcases p3975_3 (m.d 0 1) (by simp) with h3987 | h3987
                          · rcases p3975_3 (m.d 0 2) (by simp) with h3988 | h3988
                            · rcases p3975_3 (m.d 0 3) (by simp) with h3989 | h3989
                              · linarith only [h3363, h3989, hlam]
                              · rcases p3975_3 (m.d 0 4) (by simp) with h3991 | h3991
                                · linarith only [h3364, h3991, hlam]
                                · rcases p3975_3 (m.d 0 5) (by simp) with h3993 | h3993
                                  · linarith only [h3365, h3993, hlam]
                                  · linarith only [h3893, h3993, hlam]
                            · linarith only [h3367, h3988, hlam]
                          · linarith only [h3364, h3987, hlam]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          rcases p3975_3 (m.d 0 1) (by simp) with h3998 | h3998
                          · rcases p3975_3 (m.d 0 2) (by simp) with h3999 | h3999
                            · rcases p3975_3 (m.d 0 3) (by simp) with h4000 | h4000
                              · linarith only [h3363, h4000, hlam]
                              · rcases p3975_3 (m.d 0 4) (by simp) with h4002 | h4002
                                · linarith only [h3364, h4002, hlam]
                                · rcases p3975_3 (m.d 0 5) (by simp) with h4004 | h4004
                                  · linarith only [h3365, h4004, hlam]
                                  · rcases h0emin with h4006 | h4006 | h4006 | h4006 | h4006
                                    · linarith only [h0, h4006, hc12, hlam, ht01]
                                    · rcases h2bigk with h4008c | h4008c | h4008c | h4008c | h4008c | h4008c | h4008c | h4008c | h4008c | h4008c | h4008c | h4008c | h4008c | h4008c | h4008c | h4008c | h4008c | h4008c | h4008c | h4008c | h4008c | h4008c | h4008c | h4008c | h4008c
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [hlam, p4008_0]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [h0, hlam, p4008_1]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        rcases p4008_3 (m.d 0 2) (by simp) with h4011 | h4011
                                        · rcases p4008_3 (m.d 1 2) (by simp) with h4012 | h4012
                                          · rcases p4008_3 (m.d 2 3) (by simp) with h4013 | h4013
                                            · linarith only [h4013, hlam, p4008_0]
                                            · rcases p4008_3 (m.d 2 4) (by simp) with h4015 | h4015
                                              · linarith only [h3367, h4015, hlam]
                                              · linarith only [h3967, h4015, hlam]
                                          · linarith only [h3960, h4012, hlam]
                                        · linarith only [h4011, hlam, p4008_0]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        rcases p4008_3 (m.d 0 2) (by simp) with h4020 | h4020
                                        · rcases p4008_3 (m.d 1 2) (by simp) with h4021 | h4021
                                          · rcases p4008_3 (m.d 2 3) (by simp) with h4022 | h4022
                                            · linarith only [h3366, h4022, hlam]
                                            · rcases p4008_3 (m.d 2 4) (by simp) with h4024 | h4024
                                              · linarith only [h4024, hlam, p4008_0]
                                              · rcases p4008_3 (m.d 2 5) (by simp) with h4026 | h4026
                                                · linarith only [h3368, h4026, hlam]
                                                · linarith only [h3971, h4026, hlam]
                                          · linarith only [h3961, h4021, hlam]
                                        · linarith only [h4020, hlam, p4008_0]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        rcases p4008_3 (m.d 0 2) (by simp) with h4031 | h4031
                                        · rcases p4008_3 (m.d 1 2) (by simp) with h4032 | h4032
                                          · rcases p4008_3 (m.d 2 3) (by simp) with h4033 | h4033
                                            · linarith only [h3366, h4033, hlam]
                                            · rcases p4008_3 (m.d 2 4) (by simp) with h4035 | h4035
                                              · linarith only [h3367, h4035, hlam]
                                              · rcases p4008_3 (m.d 2 5) (by simp) with h4037 | h4037
                                                · linarith only [h4037, hlam, p4008_0]
                                                · rcases h2emin with h4039 | h4039 | h4039 | h4039 | h4039
                                                  · rcases h3bigk with h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c | h4040c
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [hlam, p4040_0]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [h0, h3369, h3893, h3960, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3975_1, p4040_1]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [h0, h3369, h3893, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3975_1, p4040_1]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [h3369, hlam, p4040_0]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [h3828, hlam, p4040_0]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [h3363, hlam, p4040_0]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [hlam, p4040_0]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [hc23, hlam, hphi, p4040_1, u3elo1]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [h3963, hlam, p4040_0]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [h3965, hlam, p4040_0]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [h3366, hlam, p4040_0]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [h3960, hlam, p4040_0]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [hlam, p4040_0]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [h3967, hlam, p4040_0]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [h3969, hlam, p4040_0]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [h3973, hc03, hc45, hlam, hphi, ht34, p4040_1]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [h3960, h3973, hc23, hc45, hlam, hphi, ht34, p4040_1]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [h3973, hc23, hc45, hlam, hphi, ht34, p4040_1]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [hlam, p4040_0]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [h3973, hlam, p4040_1]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [h3363, h3960, hc23, hlam, hphi, p4040_1, u3elo4]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [h3960, hc23, hlam, hphi, p4040_1, u3elo4]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [hc23, hlam, hphi, p4040_1, u3elo4]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [h3363, h3369, h3960, hc23, hlam, hphi, p4040_1, u3elo4]
                                                    · have p4040_0 := h4040c.1
                                                      have p4040_1 := h4040c.2.1
                                                      have p4040_2 := h4040c.2.2.1
                                                      have p4040_3 := h4040c.2.2.2
                                                      linarith only [hlam, p4040_0]
                                                  · rcases h3bigk with h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c | h4066c
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [hlam, p4066_0]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [h3369, h3960, hc23, hlam, hphi, p4066_1, u3elo3]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [h3369, hc23, hlam, hphi, p4066_1, u3elo3]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [h3369, hlam, p4066_0]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [h3828, hlam, p4066_0]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [h3363, hlam, p4066_0]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [hlam, p4066_0]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [hc23, hlam, hphi, p4066_1, u3elo1]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [h3963, hlam, p4066_0]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [h3965, hlam, p4066_0]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [h3366, hlam, p4066_0]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [h3960, hlam, p4066_0]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [hlam, p4066_0]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [h3967, hlam, p4066_0]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [h3969, hlam, p4066_0]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [hc03, hlam, hphi, p4066_1, u3elo3]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [h3960, hc23, hlam, hphi, p4066_1, u3elo3]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [hc23, hlam, hphi, p4066_1, u3elo3]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [hlam, p4066_0]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [h3973, hlam, p4066_1]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [h3363, h3960, hc23, hlam, hphi, p4066_1, u3elo4]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [h3960, hc23, hlam, hphi, p4066_1, u3elo4]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [hc23, hlam, hphi, p4066_1, u3elo4]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [h3363, h3369, h3960, hc23, hlam, hphi, p4066_1, u3elo4]
                                                    · have p4066_0 := h4066c.1
                                                      have p4066_1 := h4066c.2.1
                                                      have p4066_2 := h4066c.2.2.1
                                                      have p4066_3 := h4066c.2.2.2
                                                      linarith only [hlam, p4066_0]
                                                  · linarith only [h3363, h3960, h4039, hlam, ht23, u3elo0]
                                                  · linarith only [h0, h3364, h3893, h3961, h4039, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3975_1]
                                                  · linarith only [h0, h3365, h3962, h4039, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p3975_1]
                                          · linarith only [h3962, h4032, hlam]
                                        · linarith only [h4031, hlam, p4008_0]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [h4006, hc12, hlam, ht01, p4008_1]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [hlam, p4008_0]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [h0, h3363, h3369, h3893, h3960, hlam, p3975_1, p4008_2]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [h0, h3364, h3893, h3961, hlam, p3975_1, p4008_2]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [h0, h3365, h3962, hlam, p3975_1, p4008_2]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [h3366, hlam, p4008_0]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [h3960, hlam, p4008_0]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [hlam, p4008_0]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [h3967, hlam, p4008_0]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [h3969, hlam, p4008_0]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [h3367, hlam, p4008_0]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [h3961, hlam, p4008_0]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [h0, h3364, h3893, h3961, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3975_1, p4008_1]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [hlam, p4008_0]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [h3971, hlam, p4008_1]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [h3368, hlam, p4008_0]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [h3962, hlam, p4008_0]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [h0, h3365, h3962, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3975_1, p4008_1]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [h0, h3365, h3962, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3975_1, p4008_1]
                                      · have p4008_0 := h4008c.1
                                        have p4008_1 := h4008c.2.1
                                        have p4008_2 := h4008c.2.2.1
                                        have p4008_3 := h4008c.2.2.2
                                        linarith only [hlam, p4008_0]
                                    · linarith only [h0, h3369, h3893, h4006, hc12, hlam, ht01, p3975_1]
                                    · linarith only [h0, h3893, h4006, hc12, hlam, ht01, p3975_1]
                                    · linarith only [h0, h4006, hc12, hlam, ht01, p3975_1]
                            · linarith only [h3368, h3999, hlam]
                          · linarith only [h3365, h3998, hlam]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          rcases p3975_3 (m.d 0 1) (by simp) with h4122 | h4122
                          · linarith only [h0, h4122, hlam]
                          · rcases p3975_3 (m.d 0 2) (by simp) with h4124 | h4124
                            · rcases p3975_3 (m.d 0 3) (by simp) with h4125 | h4125
                              · linarith only [h3366, h4125, hlam]
                              · rcases p3975_3 (m.d 0 4) (by simp) with h4127 | h4127
                                · linarith only [h3367, h4127, hlam]
                                · rcases p3975_3 (m.d 0 5) (by simp) with h4129 | h4129
                                  · linarith only [h3368, h4129, hlam]
                                  · rcases h0emin with h4131 | h4131 | h4131 | h4131 | h4131
                                    · linarith only [h0, h4131, hc12, hlam, ht01, p3975_1]
                                    · rcases h2bigk with h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c | h4133c
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [hlam, p4133_0]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h0, hlam, p4133_1]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h3363, h3960, hlam, p3975_1, p4133_2]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h3364, h3961, hlam, p3975_1, p4133_2]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h3365, h3962, hlam, p3975_1, p4133_2]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h3363, h3960, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3975_1, p4133_1]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [hlam, p4133_0]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h0, h3363, h3960, hlam, p3975_1, p4133_2]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h0, h3364, h3961, hlam, p3975_1, p4133_2]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h0, h3365, h3962, hlam, p3975_1, p4133_2]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h3366, hlam, p4133_0]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h3960, hlam, p4133_0]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [hlam, p4133_0]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h3967, hlam, p4133_0]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h3969, hlam, p4133_0]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h3367, hlam, p4133_0]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h3961, hlam, p4133_0]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h3364, h3961, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3975_1, p4133_1]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [hlam, p4133_0]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h3971, hlam, p4133_1]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h3368, hlam, p4133_0]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h3962, hlam, p4133_0]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h0, h3365, h3962, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3975_1, p4133_1]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [h0, h3365, h3962, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3975_1, p4133_1]
                                      · have p4133_0 := h4133c.1
                                        have p4133_1 := h4133c.2.1
                                        have p4133_2 := h4133c.2.2.1
                                        have p4133_3 := h4133c.2.2.2
                                        linarith only [hlam, p4133_0]
                                    · linarith only [h4131, hlam, ht01, ht12, ht23, u3elo0]
                                    · linarith only [h0, h3364, h4131, hc12, hlam, ht01, p3975_1]
                                    · linarith only [h0, h3365, h4131, hc12, hlam, ht01, p3975_1]
                            · linarith only [h0, h4124, hlam]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          linarith only [hlam, p3975_0]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          rcases p3975_3 (m.d 0 1) (by simp) with h4164 | h4164
                          · linarith only [h0, h4164, hlam]
                          · linarith only [h3363, h4164, hlam]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          rcases p3975_3 (m.d 0 1) (by simp) with h4167 | h4167
                          · linarith only [h0, h4167, hlam]
                          · linarith only [h3364, h4167, hlam]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          rcases p3975_3 (m.d 0 1) (by simp) with h4170 | h4170
                          · linarith only [h0, h4170, hlam]
                          · linarith only [h3365, h4170, hlam]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          linarith only [h3363, hlam, p3975_1]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          linarith only [h3366, hlam, p3975_1]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          linarith only [hlam, p3975_0]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          linarith only [h3369, hlam, p3975_1]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          linarith only [h3828, hlam, p3975_1]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          linarith only [h3364, hlam, p3975_0]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          linarith only [h3367, hlam, p3975_0]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          linarith only [h3363, h3369, h3973, hc13, hc45, hlam, hphi, ht34, p3975_1]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          linarith only [hlam, p3975_0]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          linarith only [h3893, hlam, p3975_0]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          linarith only [h3365, hlam, p3975_0]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          linarith only [h3368, hlam, p3975_1]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          linarith only [h3363, h3828, hc13, hlam, hphi, p3975_1, u3elo4]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          linarith only [h3363, h3369, h3828, hc13, hlam, hphi, p3975_1, u3elo4]
                        · have p3975_0 := h3975c.1
                          have p3975_1 := h3975c.2.1
                          have p3975_2 := h3975c.2.2.1
                          have p3975_3 := h3975c.2.2.2
                          linarith only [hlam, p3975_0]
          · linarith only [h0, h3368, h3962, hlam]
        · linarith only [h0, h3367, h3961, hlam]
      · linarith only [h0, h3960, hc01, hlam, hphi, ht12, ht23, u3elo2]

set_option maxHeartbeats 5514000 in
set_option maxHeartbeats 5514000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3363 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h3364 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3365 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3366 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3367 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3368 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 3 4 (by decide) (by decide) with h3369 | h3369
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 h3363 h3364 h3365 h3366 h3367 h3368 h3369
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 h3363 h3364 h3365 h3366 h3367 h3368 h3369

set_option maxHeartbeats 5514000 in
set_option maxHeartbeats 5514000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3363 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h3364 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3365 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3366 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3367 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h3368 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  linarith only [h0, h3365, h3368, hlam]

set_option maxHeartbeats 5514000 in
set_option maxHeartbeats 5514000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3363 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h3364 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3365 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3366 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3367 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h3368 | h3368
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 h3363 h3364 h3365 h3366 h3367 h3368
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 h3363 h3364 h3365 h3366 h3367 h3368

set_option maxHeartbeats 5514000 in
set_option maxHeartbeats 5514000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3363 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h3364 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3365 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3366 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h3367 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  linarith only [h0, h3364, h3367, hlam]

set_option maxHeartbeats 5514000 in
set_option maxHeartbeats 5514000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3363 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h3364 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3365 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3366 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 4 (by decide) (by decide) with h3367 | h3367
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 h3363 h3364 h3365 h3366 h3367
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 h3363 h3364 h3365 h3366 h3367

set_option maxHeartbeats 5514000 in
set_option maxHeartbeats 5514000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3363 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h3364 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3365 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3366 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  linarith only [h0, h3363, h3366, hc13, hlam, hphi, u3elo2]

set_option maxHeartbeats 5514000 in
set_option maxHeartbeats 5514000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3363 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h3364 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3365 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h3366 | h3366
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x0_x0 m hb0 hb2 hb3 hg0 h3363 h3364 h3365 h3366
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x0_x1 m hb0 hb2 hb3 hg0 h3363 h3364 h3365 h3366

set_option maxHeartbeats 5514000 in
set_option maxHeartbeats 5514000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3363 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h3364 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3365 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 3 (by decide) (by decide) with h4194 | h4194
  · rcases m.htr 0 2 4 (by decide) (by decide) with h4195 | h4195
    · rcases m.htr 0 2 5 (by decide) (by decide) with h4196 | h4196
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4197 | h4197
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4198 | h4198
          · linarith only [h3363, h3365, h4198, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4200 | h4200
            · linarith only [h3363, h3365, h4197, h4200, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4202 | h4202
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4203 | h4203
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4204 | h4204
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4205 | h4205
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4206 | h4206
                      · linarith only [h3363, h3365, h4198, h4204, h4206, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h3363, h3365, h4206, hc13, hlam, hphi, u3elo4]
                    · linarith only [h4197, h4202, h4205, hc23, hlam, hphi, u3elo0]
                  · linarith only [h0, h3363, h4196, h4202, h4204, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h4195, h4203, hlam]
              · linarith only [h0, h4202, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4213 | h4213
          · linarith only [h3364, h3365, h4197, h4213, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4215 | h4215
            · linarith only [h3364, h3365, h4215, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4217 | h4217
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4218 | h4218
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4219 | h4219
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4220 | h4220
                    · linarith only [h3363, h3365, h4197, h4219, h4220, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4222 | h4222
                      · linarith only [h3363, h3365, h4213, h4222, hlam]
                      · linarith only [h3364, h3365, h4217, h4220, h4222, hc23, hlam, hphi, u3elo4]
                  · linarith only [h0, h4196, h4219, hlam]
                · linarith only [h0, h4195, h4218, hlam]
              · linarith only [h0, h4217, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h4228 | h4228
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4229 | h4229
          · linarith only [h0, h3363, h4196, h4229, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4231 | h4231
            · linarith only [h0, h3363, h4196, h4228, h4231, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4233 | h4233
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4234 | h4234
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4235 | h4235
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4236 | h4236
                    · linarith only [h0, h3363, h4196, h4235, h4236, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h4228, h4229, h4233, h4236, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4239 | h4239
                    · linarith only [h0, h3363, h4235, h4239, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h4228, h4229, h4233, h4239, hc23, hlam, hphi, u3elo4]
                · linarith only [h0, h3363, h4195, h4233, h4234, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h3363, h4233, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h4244 | h4244
          · linarith only [h4194, h4196, h4228, h4244, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h4246 | h4246
            · linarith only [h0, h3364, h4196, h4246, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h4248 | h4248
              · rcases m.htr 1 2 4 (by decide) (by decide) with h4249 | h4249
                · rcases m.htr 1 2 5 (by decide) (by decide) with h4250 | h4250
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4251 | h4251
                    · linarith only [h4228, h4251, hc03, hlam, hphi, u3elo1]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4253 | h4253
                      · linarith only [h0, h3363, h4196, h4244, h4253, hlam]
                      · linarith only [h3364, h3365, h4248, h4251, h4253, hc23, hlam, hphi, u3elo4]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h4256 | h4256
                    · linarith only [h0, h3363, h4228, h4250, h4256, hc03, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h4258 | h4258
                      · linarith only [h0, h3363, h4250, h4258, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h3364, h4248, h4250, h4256, h4258, hc23, hlam, hphi, u3elo4]
                · linarith only [h0, h3364, h4195, h4196, h4249, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h4248, hc01, hlam, hphi, ht12, ht23, u3elo2]
    · linarith only [h0, h3364, h4195, hlam]
  · linarith only [h0, h3363, h4194, hc13, hlam, hphi, u3elo2]

set_option maxHeartbeats 5514000 in
set_option maxHeartbeats 5514000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3363 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h3364 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h3365 | h3365
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x0 m hb0 hb2 hb3 hg0 h3363 h3364 h3365
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0_x1 m hb0 hb2 hb3 hg0 h3363 h3364 h3365

set_option maxHeartbeats 5514000 in
set_option maxHeartbeats 5514000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3363 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h3364 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h4265 | h4265
  · rcases m.htr 0 2 3 (by decide) (by decide) with h4266 | h4266
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4267 | h4267
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4268 | h4268
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4269 | h4269
          · linarith only [h3363, h3364, h4269, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4271 | h4271
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4272 | h4272
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4273 | h4273
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4274 | h4274
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4275 | h4275
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4276 | h4276
                      · linarith only [h3363, h3364, h4269, h4274, h4276, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h3363, h3364, h4276, hc13, hlam, hphi, u3elo3]
                    · linarith only [h0, h3363, h4268, h4273, h4275, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h4267, h4274, hlam]
                · linarith only [h0, h3363, h4273, hc13, hlam, hphi, u3elo2]
              · linarith only [h3363, h3364, h4271, h4272, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4283 | h4283
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4284 | h4284
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4285 | h4285
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4286 | h4286
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4287 | h4287
                      · linarith only [h3363, h3364, h4269, h4285, h4287, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h3363, h3364, h4284, h4287, hc23, hlam, hphi, u3elo3]
                    · linarith only [h3363, h3364, h4268, h4284, h4285, h4286, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h3363, h4267, h4284, h4285, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h4284, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h3364, h4265, h4283, hlam]
        · linarith only [h0, h4265, h4268, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4295 | h4295
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4296 | h4296
          · linarith only [h0, h3363, h4267, h4296, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4298 | h4298
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4299 | h4299
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4300 | h4300
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4301 | h4301
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4302 | h4302
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4303 | h4303
                      · linarith only [h0, h3363, h4267, h4296, h4301, h4303, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h3363, h4267, h4301, h4303, hc13, hlam, hphi, u3elo3]
                    · linarith only [h0, h3363, h4267, h4300, h4301, h4302, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4307 | h4307
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4308 | h4308
                      · linarith only [h0, h3363, h4267, h4296, h4301, h4308, hc02, hc24, hlam, hphi]
                      · linarith only [h3363, h3364, h4300, h4308, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h3363, h4295, h4300, h4307, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h3363, h4300, hc13, hlam, hphi, u3elo2]
              · linarith only [h0, h3363, h4267, h4298, h4299, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4314 | h4314
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4315 | h4315
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4316 | h4316
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4317 | h4317
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4318 | h4318
                      · linarith only [h0, h3363, h4267, h4296, h4316, h4318, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h3363, h3364, h4315, h4318, hc23, hlam, hphi, u3elo3]
                    · linarith only [h4267, h4316, h4317, hc02, hc25, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4322 | h4322
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4323 | h4323
                      · linarith only [h0, h3363, h4316, h4323, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h3363, h4315, h4316, h4323, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h3363, h4295, h4315, h4322, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h4315, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h0, h4265, h4267, h4314, hlam]
        · linarith only [h0, h4265, h4295, hlam]
    · linarith only [h0, h3363, h4266, hc13, hlam, hphi, u3elo2]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h4331 | h4331
    · rcases m.htr 0 2 4 (by decide) (by decide) with h4332 | h4332
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4333 | h4333
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4334 | h4334
          · linarith only [h3363, h3364, h4334, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4336 | h4336
            · linarith only [h3363, h4265, h4336, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4338 | h4338
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4339 | h4339
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4340 | h4340
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4341 | h4341
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4342 | h4342
                      · linarith only [h3363, h3364, h4334, h4340, h4342, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h3363, h3364, h4339, h4342, hc23, hlam, hphi, u3elo3]
                    · linarith only [h3363, h3364, h4333, h4339, h4340, h4341, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h4332, h4340, hlam]
                · linarith only [h0, h4339, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4348 | h4348
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4349 | h4349
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4350 | h4350
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4351 | h4351
                      · linarith only [h3363, h3364, h4338, h4351, hc34, hc45, hlam, hphi]
                      · linarith only [h3363, h3364, h4351, hc13, hlam, hphi, u3elo3]
                    · linarith only [h0, h4333, h4350, hlam]
                  · linarith only [h0, h4332, h4349, hlam]
                · linarith only [h0, h4348, hc01, hlam, hphi, ht12, ht23, u3elo2]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4357 | h4357
          · linarith only [h3363, h3364, h4357, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4359 | h4359
            · linarith only [h3363, h4265, h4359, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4361 | h4361
              · linarith only [h4332, h4333, h4361, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4363 | h4363
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4364 | h4364
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4365 | h4365
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4366 | h4366
                      · linarith only [h3363, h3364, h4332, h4333, h4357, h4365, h4366, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h3363, h3364, h4363, h4366, hc23, hlam, hphi, u3elo3]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4369 | h4369
                      · linarith only [h3363, h3364, h4361, h4369, hc34, hc45, hlam, hphi]
                      · linarith only [h3363, h3364, h4369, hc13, hlam, hphi, u3elo3]
                  · linarith only [h0, h3363, h4332, h4363, h4364, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h3363, h4363, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4374 | h4374
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4375 | h4375
          · linarith only [h0, h3363, h4332, h4375, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4377 | h4377
            · linarith only [h3363, h4265, h4375, h4377, hc13, hlam, hphi, u3elo3]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4379 | h4379
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4380 | h4380
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4381 | h4381
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4382 | h4382
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4383 | h4383
                      · linarith only [h3363, h4265, h4332, h4374, h4375, h4381, h4383, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h0, h3363, h4332, h4380, h4381, h4383, hc23, hlam, hphi, u3elo3]
                    · linarith only [h4332, h4374, h4381, h4382, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4387 | h4387
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4388 | h4388
                      · linarith only [h0, h3363, h4381, h4388, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h3363, h3364, h4380, h4388, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h3363, h4332, h4374, h4380, h4387, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h3363, h4380, hc13, hlam, hphi, u3elo2]
              · linarith only [h4332, h4374, h4379, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h4394 | h4394
          · linarith only [h0, h3363, h4332, h4394, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h4396 | h4396
            · linarith only [h3363, h4265, h4396, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h4398 | h4398
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4399 | h4399
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4400 | h4400
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4401 | h4401
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4402 | h4402
                      · linarith only [h0, h3363, h4332, h4394, h4400, h4402, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h3363, h3364, h4399, h4402, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h3363, h4332, h4399, h4400, h4401, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4406 | h4406
                    · linarith only [h0, h3363, h4374, h4399, h4400, h4406, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4408 | h4408
                      · linarith only [h0, h3363, h4394, h4398, h4400, h4408, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h3363, h4400, h4408, hc13, hlam, hphi, u3elo3]
                · linarith only [h0, h3363, h4399, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h4412 | h4412
                · rcases m.htr 1 2 4 (by decide) (by decide) with h4413 | h4413
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4414 | h4414
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4415 | h4415
                      · linarith only [h0, h3363, h4332, h4413, h4415, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h3363, h4332, h4412, h4413, h4415, hc23, hlam, hphi, u3elo3]
                    · linarith only [h0, h3363, h4332, h4412, h4413, h4414, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h4419 | h4419
                    · linarith only [h0, h3363, h4374, h4412, h4413, h4419, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h4421 | h4421
                      · linarith only [h0, h3363, h4332, h4398, h4421, hc34, hc45, hlam, hphi]
                      · linarith only [h0, h3363, h4412, h4413, h4421, hc23, hlam, hphi, u3elo3]
                · linarith only [h0, h4412, hc01, hlam, hphi, ht12, ht23, u3elo2]
    · linarith only [h0, h3363, h4331, hc13, hlam, hphi, u3elo2]

set_option maxHeartbeats 5514000 in
set_option maxHeartbeats 5514000 in
theorem r1l7_10_12_23_L_I_L_I_M_LI_s5_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h3363 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h3364 | h3364
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x0 m hb0 hb2 hb3 hg0 h3363 h3364
  · exact r1l7_10_12_23_L_I_L_I_M_LI_s5_x0_x1 m hb0 hb2 hb3 hg0 h3363 h3364

end R2N4
