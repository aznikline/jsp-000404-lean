import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_7S2
import Jsp000404.R1LeavesN7_7S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7178000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s8_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h2202 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 4 (by decide) (by decide) with h2806 | h2806
  · rcases m.htr 1 2 5 (by decide) (by decide) with h2807 | h2807
    · linarith only [h0, h2202, h2807, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2809 | h2809
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2810 | h2810
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2811 | h2811
          · linarith only [h2, h2811, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2813 | h2813
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2814 | h2814
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2815 | h2815
                · linarith only [h2806, h2807, h2815, h6, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2817 | h2817
                  · linarith only [h2806, h2807, h2813, h2817, h6, h9, hlam]
                  · rcases h1bigk with h2819c | h2819c | h2819c | h2819c | h2819c | h2819c | h2819c | h2819c | h2819c | h2819c | h2819c | h2819c | h2819c | h2819c | h2819c | h2819c | h2819c | h2819c | h2819c | h2819c | h2819c | h2819c | h2819c | h2819c | h2819c
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [hlam, p2819_0]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      rcases p2819_3 (m.d 0 1) (by simp) with h2821 | h2821
                      · rcases p2819_3 (m.d 1 2) (by simp) with h2822 | h2822
                        · linarith only [h2822, hlam, p2819_0]
                        · rcases p2819_3 (m.d 1 3) (by simp) with h2824 | h2824
                          · linarith only [h1, h2824, hlam]
                          · linarith only [h2202, h2824, hlam]
                      · linarith only [h2821, hlam, p2819_0]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [h2810, hc01, hlam, hphi, ht0b, ht5b, p2819_1, u5ehi3]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      rcases p2819_3 (m.d 0 1) (by simp) with h2829 | h2829
                      · rcases p2819_3 (m.d 1 2) (by simp) with h2830 | h2830
                        · linarith only [h0, h2830, hlam]
                        · linarith only [h2806, h2830, hlam]
                      · linarith only [h2829, hlam, p2819_0]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      rcases p2819_3 (m.d 0 1) (by simp) with h2834 | h2834
                      · rcases p2819_3 (m.d 1 2) (by simp) with h2835 | h2835
                        · linarith only [h0, h2835, hlam]
                        · rcases p2819_3 (m.d 1 3) (by simp) with h2837 | h2837
                          · linarith only [h1, h2837, hlam]
                          · linarith only [h2810, h2837, hlam]
                      · linarith only [h2834, hlam, p2819_0]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [h0, hlam, p2819_0]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [hlam, p2819_0]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [h2202, hlam, p2819_0]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [h0, h2807, h2814, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p2819_1]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [h2807, hlam, p2819_0]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [h1, hlam, p2819_0]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [h1, h2806, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p2819_1]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [hlam, p2819_0]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      rcases p2819_3 (m.d 0 1) (by simp) with h2849 | h2849
                      · rcases p2819_3 (m.d 1 2) (by simp) with h2850 | h2850
                        · linarith only [h2202, h2850, hlam]
                        · linarith only [h2806, h2850, hlam]
                      · linarith only [h2, h2849, hlam]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [h0, h2202, h4, hc01, hlam, hphi, ht0b, ht5b, p2819_1, u5ehi1]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [h2, hlam, p2819_0]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [h2806, hlam, p2819_1]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [h2809, hlam, p2819_0]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [hlam, p2819_0]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [h2811, hlam, p2819_1]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [h3, hlam, p2819_0]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [h2806, h2813, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2819_1]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [h2810, hlam, p2819_0]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      rcases p2819_3 (m.d 0 1) (by simp) with h2863 | h2863
                      · rcases p2819_3 (m.d 1 2) (by simp) with h2864 | h2864
                        · linarith only [h2807, h2864, hlam]
                        · linarith only [h2806, h2864, hlam]
                      · linarith only [h2, h2863, hlam]
                    · have p2819_0 := h2819c.1
                      have p2819_1 := h2819c.2.1
                      have p2819_2 := h2819c.2.2.1
                      have p2819_3 := h2819c.2.2.2
                      linarith only [hlam, p2819_0]
              · linarith only [h0, h2202, h2806, h2813, h2814, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h2202, h2810, h2813, h4, h7, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2871 | h2871
          · linarith only [h2, h2806, h2807, h2871, h6, h9, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2873 | h2873
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2874 | h2874
              · linarith only [h0, h2202, h2806, h2810, h2873, h2874, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h2202, h2806, h2873, h2874, h8, h9, hc34, hc45, hlam, hphi]
            · linarith only [h0, h2202, h2806, h2873, h4, h7, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
      · linarith only [h2202, h2806, h2809, h7, h9, hc24, hc45, hlam, hphi]
  · rcases m.htr 1 2 5 (by decide) (by decide) with h2879 | h2879
    · linarith only [h2806, h2879, h5, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
    · rcases m.htr 1 3 4 (by decide) (by decide) with h2881 | h2881
      · rcases m.htr 1 3 5 (by decide) (by decide) with h2882 | h2882
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2883 | h2883
          · linarith only [h2, h2806, h2883, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2885 | h2885
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2886 | h2886
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2887 | h2887
                · linarith only [h2887, h5, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2889 | h2889
                  · linarith only [h2806, h2889, h5, h9, hc12, hc34, hlam, hphi, ht23]
                  · rcases h1bigk with h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c | h2891c
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      rcases p2891_3 (m.d 0 1) (by simp) with h2893 | h2893
                      · rcases p2891_3 (m.d 1 2) (by simp) with h2894 | h2894
                        · linarith only [h2894, hlam, p2891_0]
                        · rcases p2891_3 (m.d 1 3) (by simp) with h2896 | h2896
                          · linarith only [h1, h2896, hlam]
                          · linarith only [h2202, h2896, hlam]
                      · linarith only [h2893, hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2882, hc01, hlam, hphi, ht0b, ht5b, p2891_1, u5ehi3]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      rcases p2891_3 (m.d 0 1) (by simp) with h2901 | h2901
                      · rcases p2891_3 (m.d 1 2) (by simp) with h2902 | h2902
                        · linarith only [h0, h2902, hlam]
                        · rcases p2891_3 (m.d 1 3) (by simp) with h2904 | h2904
                          · linarith only [h1, h2904, hlam]
                          · linarith only [h2881, h2904, hlam]
                      · linarith only [h2901, hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      rcases p2891_3 (m.d 0 1) (by simp) with h2908 | h2908
                      · rcases p2891_3 (m.d 1 2) (by simp) with h2909 | h2909
                        · linarith only [h0, h2909, hlam]
                        · rcases p2891_3 (m.d 1 3) (by simp) with h2911 | h2911
                          · linarith only [h1, h2911, hlam]
                          · linarith only [h2882, h2911, hlam]
                      · linarith only [h2908, hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h0, hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2202, hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2806, hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2879, hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h1, hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      rcases p2891_3 (m.d 0 1) (by simp) with h2921 | h2921
                      · rcases p2891_3 (m.d 1 2) (by simp) with h2922 | h2922
                        · linarith only [h2202, h2922, hlam]
                        · rcases p2891_3 (m.d 1 3) (by simp) with h2924 | h2924
                          · rcases p2891_3 (m.d 1 4) (by simp) with h2925 | h2925
                            · linarith only [h2881, h2925, hlam]
                            · linarith only [h2806, h2925, hlam]
                          · linarith only [h2202, h2924, hlam]
                      · linarith only [h0, h2921, hlam]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      rcases p2891_3 (m.d 0 1) (by simp) with h2931 | h2931
                      · rcases p2891_3 (m.d 1 2) (by simp) with h2932 | h2932
                        · linarith only [h2202, h2932, hlam]
                        · rcases p2891_3 (m.d 1 3) (by simp) with h2934 | h2934
                          · rcases p2891_3 (m.d 1 4) (by simp) with h2935 | h2935
                            · linarith only [h2881, h2935, hlam]
                            · rcases p2891_3 (m.d 1 5) (by simp) with h2937 | h2937
                              · linarith only [h2882, h2937, hlam]
                              · linarith only [h2883, h2937, hlam]
                          · linarith only [h2881, h2934, hlam]
                      · linarith only [h2, h2931, hlam]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h0, h2202, h4, hc01, hlam, hphi, ht0b, ht5b, p2891_1, u5ehi1]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2, hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2, h9, hc12, hc45, hlam, hphi, ht23, ht34, p2891_1]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2881, hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2883, hlam, p2891_1]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h3, hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      rcases p2891_3 (m.d 0 1) (by simp) with h2949 | h2949
                      · rcases p2891_3 (m.d 1 2) (by simp) with h2950 | h2950
                        · linarith only [h2879, h2950, hlam]
                        · rcases p2891_3 (m.d 1 3) (by simp) with h2952 | h2952
                          · rcases p2891_3 (m.d 1 4) (by simp) with h2953 | h2953
                            · linarith only [h2883, h2953, hlam]
                            · linarith only [h2806, h2953, hlam]
                          · linarith only [h2202, h2952, hlam]
                      · linarith only [h0, h2949, hlam]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [h2882, hlam, p2891_0]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      rcases p2891_3 (m.d 0 1) (by simp) with h2959 | h2959
                      · rcases p2891_3 (m.d 1 2) (by simp) with h2960 | h2960
                        · linarith only [h2879, h2960, hlam]
                        · rcases p2891_3 (m.d 1 3) (by simp) with h2962 | h2962
                          · rcases p2891_3 (m.d 1 4) (by simp) with h2963 | h2963
                            · linarith only [h2883, h2963, hlam]
                            · rcases p2891_3 (m.d 1 5) (by simp) with h2965 | h2965
                              · rcases h1emax with h2966 | h2966 | h2966 | h2966 | h2966
                                · linarith only [h0, h2879, h2886, h2966, h4, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p2891_1]
                                · rcases h3bigk with h2968c | h2968c | h2968c | h2968c | h2968c | h2968c | h2968c | h2968c | h2968c | h2968c | h2968c | h2968c | h2968c | h2968c | h2968c | h2968c | h2968c | h2968c | h2968c | h2968c | h2968c | h2968c | h2968c | h2968c | h2968c
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [hlam, p2968_0]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [h0, h2882, h4, hc01, hlam, hphi, ht0b, ht5b, p2968_1, u5ehi3]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [h0, h2806, h2879, h2886, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2891_1, p2968_1]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    rcases p2968_3 (m.d 0 3) (by simp) with h2972 | h2972
                                    · rcases p2968_3 (m.d 1 3) (by simp) with h2973 | h2973
                                      · linarith only [h1, h2973, hlam]
                                      · linarith only [h2881, h2973, hlam]
                                    · linarith only [h2972, hlam, p2968_0]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    rcases p2968_3 (m.d 0 3) (by simp) with h2977 | h2977
                                    · rcases p2968_3 (m.d 1 3) (by simp) with h2978 | h2978
                                      · linarith only [h1, h2978, hlam]
                                      · linarith only [h2882, h2978, hlam]
                                    · linarith only [h2977, hlam, p2968_0]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [h1, hlam, p2968_0]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [hlam, p2968_0]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [h2202, hlam, p2968_1]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    rcases p2968_3 (m.d 0 3) (by simp) with h2985 | h2985
                                    · rcases p2968_3 (m.d 1 3) (by simp) with h2986 | h2986
                                      · rcases p2968_3 (m.d 2 3) (by simp) with h2987 | h2987
                                        · rcases p2968_3 (m.d 3 4) (by simp) with h2988 | h2988
                                          · linarith only [h2988, hlam, p2968_0]
                                          · rcases p2968_3 (m.d 3 5) (by simp) with h2990 | h2990
                                            · linarith only [h2882, h2990, hlam]
                                            · linarith only [h2889, h2990, hlam]
                                        · linarith only [h2885, h2987, hlam]
                                      · linarith only [h2986, hlam, p2968_0]
                                    · linarith only [h2985, h7, hlam]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p2968_1, u5ehi3]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [h4, hlam, p2968_0]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [h0, h2881, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2968_1]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [hlam, p2968_0]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    rcases p2968_3 (m.d 0 3) (by simp) with h3000 | h3000
                                    · rcases p2968_3 (m.d 1 3) (by simp) with h3001 | h3001
                                      · linarith only [h2202, h3001, hlam]
                                      · linarith only [h2881, h3001, hlam]
                                    · linarith only [h3000, h7, hlam]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p2968_1, u5ehi3]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [h7, hlam, p2968_0]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [h2881, hlam, p2968_0]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [h2885, hlam, p2968_0]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [hlam, p2968_0]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [h2889, hlam, p2968_1]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [h8, hlam, p2968_0]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [h2882, hlam, p2968_0]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [h2886, hlam, p2968_0]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [h1, h2882, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p2968_1]
                                  · have p2968_0 := h2968c.1
                                    have p2968_1 := h2968c.2.1
                                    have p2968_2 := h2968c.2.2.1
                                    have p2968_3 := h2968c.2.2.2
                                    linarith only [hlam, p2968_0]
                                · linarith only [h2882, h2966, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                · rcases h3bigk with h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c | h3017c
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [hlam, p3017_0]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [h2806, h2882, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2891_1, p3017_1]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [h0, h2202, h2806, h2882, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p2891_1, p3017_1]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    rcases p3017_3 (m.d 0 3) (by simp) with h3021 | h3021
                                    · rcases p3017_3 (m.d 1 3) (by simp) with h3022 | h3022
                                      · linarith only [h1, h3022, hlam]
                                      · linarith only [h2881, h3022, hlam]
                                    · linarith only [h3021, hlam, p3017_0]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    rcases p3017_3 (m.d 0 3) (by simp) with h3026 | h3026
                                    · rcases p3017_3 (m.d 1 3) (by simp) with h3027 | h3027
                                      · linarith only [h1, h3027, hlam]
                                      · linarith only [h2882, h3027, hlam]
                                    · linarith only [h3026, hlam, p3017_0]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [h1, hlam, p3017_0]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [hlam, p3017_0]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [h2202, hlam, p3017_1]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    rcases p3017_3 (m.d 0 3) (by simp) with h3034 | h3034
                                    · rcases p3017_3 (m.d 1 3) (by simp) with h3035 | h3035
                                      · rcases p3017_3 (m.d 2 3) (by simp) with h3036 | h3036
                                        · rcases p3017_3 (m.d 3 4) (by simp) with h3037 | h3037
                                          · linarith only [h3037, hlam, p3017_0]
                                          · rcases p3017_3 (m.d 3 5) (by simp) with h3039 | h3039
                                            · linarith only [h2882, h3039, hlam]
                                            · linarith only [h2889, h3039, hlam]
                                        · linarith only [h2885, h3036, hlam]
                                      · linarith only [h3035, hlam, p3017_0]
                                    · linarith only [h3034, h7, hlam]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p3017_1, u5ehi3]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [h4, hlam, p3017_0]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [h0, h2881, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3017_1]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [hlam, p3017_0]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    rcases p3017_3 (m.d 0 3) (by simp) with h3049 | h3049
                                    · rcases p3017_3 (m.d 1 3) (by simp) with h3050 | h3050
                                      · linarith only [h2202, h3050, hlam]
                                      · linarith only [h2881, h3050, hlam]
                                    · linarith only [h3049, h7, hlam]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p3017_1, u5ehi3]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [h7, hlam, p3017_0]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [h2881, hlam, p3017_0]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [h2885, hlam, p3017_0]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [hlam, p3017_0]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [h2889, hlam, p3017_1]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [h8, hlam, p3017_0]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [h2882, hlam, p3017_0]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [h2886, hlam, p3017_0]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [h1, h2882, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3017_1]
                                  · have p3017_0 := h3017c.1
                                    have p3017_1 := h3017c.2.1
                                    have p3017_2 := h3017c.2.2.1
                                    have p3017_3 := h3017c.2.2.2
                                    linarith only [hlam, p3017_0]
                                · linarith only [h2806, h2966, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p2891_1]
                              · linarith only [h2883, h2965, hlam]
                          · linarith only [h2881, h2962, hlam]
                      · linarith only [h2, h2959, hlam]
                    · have p2891_0 := h2891c.1
                      have p2891_1 := h2891c.2.1
                      have p2891_2 := h2891c.2.2.1
                      have p2891_3 := h2891c.2.2.2
                      linarith only [hlam, p2891_0]
              · linarith only [h2202, h2882, h2886, hlam]
            · linarith only [h2202, h2882, h2885, h7, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3072 | h3072
          · linarith only [h2, h3072, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3074 | h3074
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3075 | h3075
              · linarith only [h0, h2881, h2882, h3075, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3077 | h3077
                · linarith only [h3074, h3075, h3077, h8, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3079 | h3079
                  · linarith only [h2806, h2881, h3074, h3075, h3079, h8, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases h1bigk with h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c | h3081c
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [hlam, p3081_0]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [h1, h2806, h3074, h3075, h8, hlam, p3081_2]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      rcases p3081_3 (m.d 0 1) (by simp) with h3084 | h3084
                      · rcases p3081_3 (m.d 1 2) (by simp) with h3085 | h3085
                        · linarith only [h0, h3085, hlam]
                        · rcases p3081_3 (m.d 1 3) (by simp) with h3087 | h3087
                          · linarith only [h3087, hlam, p3081_0]
                          · rcases p3081_3 (m.d 1 4) (by simp) with h3089 | h3089
                            · linarith only [h2, h3089, hlam]
                            · rcases p3081_3 (m.d 1 5) (by simp) with h3091 | h3091
                              · linarith only [h3, h3091, hlam]
                              · linarith only [h2882, h3091, hlam]
                      · linarith only [h3084, hlam, p3081_0]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      rcases p3081_3 (m.d 0 1) (by simp) with h3095 | h3095
                      · rcases p3081_3 (m.d 1 2) (by simp) with h3096 | h3096
                        · linarith only [h0, h3096, hlam]
                        · rcases p3081_3 (m.d 1 3) (by simp) with h3098 | h3098
                          · linarith only [h1, h3098, hlam]
                          · linarith only [h2881, h3098, hlam]
                      · linarith only [h3095, hlam, p3081_0]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      rcases p3081_3 (m.d 0 1) (by simp) with h3102 | h3102
                      · rcases p3081_3 (m.d 1 2) (by simp) with h3103 | h3103
                        · linarith only [h0, h3103, hlam]
                        · rcases p3081_3 (m.d 1 3) (by simp) with h3105 | h3105
                          · linarith only [h1, h3105, hlam]
                          · rcases p3081_3 (m.d 1 4) (by simp) with h3107 | h3107
                            · linarith only [h2, h3107, hlam]
                            · rcases p3081_3 (m.d 1 5) (by simp) with h3109 | h3109
                              · linarith only [h3109, hlam, p3081_0]
                              · rcases h1emax with h3111 | h3111 | h3111 | h3111 | h3111
                                · linarith only [h0, h2806, h3074, h3075, h3111, h4, h8, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                · rcases h3bigk with h3113c | h3113c | h3113c | h3113c | h3113c | h3113c | h3113c | h3113c | h3113c | h3113c | h3113c | h3113c | h3113c | h3113c | h3113c | h3113c | h3113c | h3113c | h3113c | h3113c | h3113c | h3113c | h3113c | h3113c | h3113c
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [hlam, p3113_0]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    rcases p3113_3 (m.d 0 3) (by simp) with h3115 | h3115
                                    · rcases p3113_3 (m.d 1 3) (by simp) with h3116 | h3116
                                      · linarith only [h1, h3116, hlam]
                                      · rcases p3113_3 (m.d 2 3) (by simp) with h3118 | h3118
                                        · linarith only [h3118, h4, hlam]
                                        · linarith only [h2202, h3118, hlam]
                                    · linarith only [h1, h3115, hlam]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    rcases p3113_3 (m.d 0 3) (by simp) with h3122 | h3122
                                    · rcases p3113_3 (m.d 1 3) (by simp) with h3123 | h3123
                                      · linarith only [h1, h3123, hlam]
                                      · rcases p3113_3 (m.d 2 3) (by simp) with h3125 | h3125
                                        · linarith only [h3125, h4, hlam]
                                        · rcases p3113_3 (m.d 3 4) (by simp) with h3127 | h3127
                                          · linarith only [h3127, h7, hlam]
                                          · rcases p3113_3 (m.d 3 5) (by simp) with h3129 | h3129
                                            · linarith only [h3129, h8, hlam]
                                            · linarith only [h3075, h3129, hlam]
                                    · linarith only [h3122, h4, hlam]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [h2202, h2881, h3075, h8, hlam, p3113_2]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [h0, h2806, h3074, h3075, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3113_1]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [h1, hlam, p3113_0]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [hlam, p3113_0]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [h2202, hlam, p3113_1]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [h2202, h3075, h8, h9, hc34, hc45, hlam, hphi, p3113_1]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [h2882, hlam, p3113_0]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [h4, hlam, p3113_0]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [h3075, hc13, hc35, hlam, hphi, p3113_1]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [hlam, p3113_0]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [h0, h3075, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3113_1]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [h3075, hlam, p3113_0]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [h7, hlam, p3113_0]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [h2881, hlam, p3113_0]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [h3074, hlam, p3113_0]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [hlam, p3113_0]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [h3079, hlam, p3113_1]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [h8, hlam, p3113_0]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [h0, h2881, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3113_1]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [h0, h2202, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3113_1]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    rcases p3113_3 (m.d 0 3) (by simp) with h3153 | h3153
                                    · rcases p3113_3 (m.d 1 3) (by simp) with h3154 | h3154
                                      · linarith only [h2882, h3154, hlam]
                                      · linarith only [h2881, h3154, hlam]
                                    · linarith only [h3153, h7, hlam]
                                  · have p3113_0 := h3113c.1
                                    have p3113_1 := h3113c.2.1
                                    have p3113_2 := h3113c.2.2.1
                                    have p3113_3 := h3113c.2.2.2
                                    linarith only [hlam, p3113_0]
                                · rcases h3bigk with h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c | h3159c
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [hlam, p3159_0]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    rcases p3159_3 (m.d 0 3) (by simp) with h3161 | h3161
                                    · rcases p3159_3 (m.d 1 3) (by simp) with h3162 | h3162
                                      · linarith only [h1, h3162, hlam]
                                      · rcases p3159_3 (m.d 2 3) (by simp) with h3164 | h3164
                                        · linarith only [h3164, h4, hlam]
                                        · linarith only [h2202, h3164, hlam]
                                    · linarith only [h1, h3161, hlam]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    rcases p3159_3 (m.d 0 3) (by simp) with h3168 | h3168
                                    · rcases p3159_3 (m.d 1 3) (by simp) with h3169 | h3169
                                      · linarith only [h1, h3169, hlam]
                                      · rcases p3159_3 (m.d 2 3) (by simp) with h3171 | h3171
                                        · linarith only [h3171, h4, hlam]
                                        · rcases p3159_3 (m.d 3 4) (by simp) with h3173 | h3173
                                          · linarith only [h3173, h7, hlam]
                                          · rcases p3159_3 (m.d 3 5) (by simp) with h3175 | h3175
                                            · linarith only [h3175, h8, hlam]
                                            · linarith only [h3075, h3175, hlam]
                                    · linarith only [h3168, h4, hlam]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [h2881, h2882, h8, hlam, p3159_2]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [h0, h2881, h2882, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3159_1]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [h1, hlam, p3159_0]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [hlam, p3159_0]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [h2202, hlam, p3159_1]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [h0, h2882, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3159_1]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [h2882, hlam, p3159_0]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [h4, hlam, p3159_0]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [h0, h2881, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3159_1]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [hlam, p3159_0]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [h0, h3075, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3159_1]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [h3075, hlam, p3159_0]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [h7, hlam, p3159_0]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [h2881, hlam, p3159_0]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [h3074, hlam, p3159_0]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [hlam, p3159_0]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [h3079, hlam, p3159_1]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [h8, hlam, p3159_0]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [h0, h2881, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3159_1]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [h0, h2202, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3159_1]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    rcases p3159_3 (m.d 0 3) (by simp) with h3199 | h3199
                                    · rcases p3159_3 (m.d 1 3) (by simp) with h3200 | h3200
                                      · linarith only [h2882, h3200, hlam]
                                      · linarith only [h2881, h3200, hlam]
                                    · linarith only [h3199, h7, hlam]
                                  · have p3159_0 := h3159c.1
                                    have p3159_1 := h3159c.2.1
                                    have p3159_2 := h3159c.2.2.1
                                    have p3159_3 := h3159c.2.2.2
                                    linarith only [hlam, p3159_0]
                                · rcases h3bigk with h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c | h3205c
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [hlam, p3205_0]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    rcases p3205_3 (m.d 0 3) (by simp) with h3207 | h3207
                                    · rcases p3205_3 (m.d 1 3) (by simp) with h3208 | h3208
                                      · linarith only [h1, h3208, hlam]
                                      · rcases p3205_3 (m.d 2 3) (by simp) with h3210 | h3210
                                        · linarith only [h3210, h4, hlam]
                                        · linarith only [h2202, h3210, hlam]
                                    · linarith only [h1, h3207, hlam]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    rcases p3205_3 (m.d 0 3) (by simp) with h3214 | h3214
                                    · rcases p3205_3 (m.d 1 3) (by simp) with h3215 | h3215
                                      · linarith only [h1, h3215, hlam]
                                      · rcases p3205_3 (m.d 2 3) (by simp) with h3217 | h3217
                                        · linarith only [h3217, h4, hlam]
                                        · rcases p3205_3 (m.d 3 4) (by simp) with h3219 | h3219
                                          · linarith only [h3219, h7, hlam]
                                          · rcases p3205_3 (m.d 3 5) (by simp) with h3221 | h3221
                                            · linarith only [h3221, h8, hlam]
                                            · linarith only [h3075, h3221, hlam]
                                    · linarith only [h3214, h4, hlam]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [h2881, h2882, h8, hlam, p3205_2]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [h0, h2881, h2882, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3205_1]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [h1, hlam, p3205_0]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [hlam, p3205_0]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [h2202, hlam, p3205_1]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [h0, h2882, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3205_1]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [h2882, hlam, p3205_0]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [h4, hlam, p3205_0]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [h0, h2881, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3205_1]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [hlam, p3205_0]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [h0, h3075, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3205_1]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [h3075, hlam, p3205_0]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [h7, hlam, p3205_0]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [h2881, hlam, p3205_0]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [h3074, hlam, p3205_0]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [hlam, p3205_0]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [h3079, hlam, p3205_1]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [h8, hlam, p3205_0]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [h0, h2881, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3205_1]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [h0, h2202, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3205_1]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    rcases p3205_3 (m.d 0 3) (by simp) with h3245 | h3245
                                    · rcases p3205_3 (m.d 1 3) (by simp) with h3246 | h3246
                                      · linarith only [h2882, h3246, hlam]
                                      · linarith only [h2881, h3246, hlam]
                                    · linarith only [h3245, h7, hlam]
                                  · have p3205_0 := h3205c.1
                                    have p3205_1 := h3205c.2.1
                                    have p3205_2 := h3205c.2.2.1
                                    have p3205_3 := h3205c.2.2.2
                                    linarith only [hlam, p3205_0]
                                · rcases h3bigk with h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c | h3251c
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [hlam, p3251_0]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    rcases p3251_3 (m.d 0 3) (by simp) with h3253 | h3253
                                    · rcases p3251_3 (m.d 1 3) (by simp) with h3254 | h3254
                                      · linarith only [h1, h3254, hlam]
                                      · rcases p3251_3 (m.d 2 3) (by simp) with h3256 | h3256
                                        · linarith only [h3256, h4, hlam]
                                        · linarith only [h2202, h3256, hlam]
                                    · linarith only [h1, h3253, hlam]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    rcases p3251_3 (m.d 0 3) (by simp) with h3260 | h3260
                                    · rcases p3251_3 (m.d 1 3) (by simp) with h3261 | h3261
                                      · linarith only [h1, h3261, hlam]
                                      · rcases p3251_3 (m.d 2 3) (by simp) with h3263 | h3263
                                        · linarith only [h3263, h4, hlam]
                                        · rcases p3251_3 (m.d 3 4) (by simp) with h3265 | h3265
                                          · linarith only [h3265, h7, hlam]
                                          · rcases p3251_3 (m.d 3 5) (by simp) with h3267 | h3267
                                            · linarith only [h3267, h8, hlam]
                                            · linarith only [h3075, h3267, hlam]
                                    · linarith only [h3260, h4, hlam]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [h2881, h2882, h8, hlam, p3251_2]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [h0, h2881, h2882, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3251_1]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [h1, hlam, p3251_0]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [hlam, p3251_0]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [h2202, hlam, p3251_1]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [h0, h2882, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3251_1]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [h2882, hlam, p3251_0]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [h4, hlam, p3251_0]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [h0, h2881, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3251_1]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [hlam, p3251_0]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [h0, h3075, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3251_1]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [h3075, hlam, p3251_0]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [h7, hlam, p3251_0]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [h2881, hlam, p3251_0]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [h3074, hlam, p3251_0]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [hlam, p3251_0]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [h3079, hlam, p3251_1]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [h8, hlam, p3251_0]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [h0, h2881, h4, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3251_1]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [h0, h2202, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3251_1]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    rcases p3251_3 (m.d 0 3) (by simp) with h3291 | h3291
                                    · rcases p3251_3 (m.d 1 3) (by simp) with h3292 | h3292
                                      · linarith only [h2882, h3292, hlam]
                                      · linarith only [h2881, h3292, hlam]
                                    · linarith only [h3291, h7, hlam]
                                  · have p3251_0 := h3251c.1
                                    have p3251_1 := h3251c.2.1
                                    have p3251_2 := h3251c.2.2.1
                                    have p3251_3 := h3251c.2.2.2
                                    linarith only [hlam, p3251_0]
                      · linarith only [h3102, hlam, p3081_0]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [h0, hlam, p3081_0]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [hlam, p3081_0]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [h2202, hlam, p3081_0]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [h2806, hlam, p3081_0]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [h2879, hlam, p3081_0]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [h1, hlam, p3081_0]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [h0, h2882, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3081_1]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [hlam, p3081_0]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [h0, h2806, h2882, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3081_1]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [h2882, hlam, p3081_1]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [h2, hlam, p3081_0]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [h2, h9, hc12, hc45, hlam, hphi, ht23, ht34, p3081_1]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [h2881, hlam, p3081_0]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [hlam, p3081_0]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [h3072, hlam, p3081_1]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [h3, hlam, p3081_0]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      rcases p3081_3 (m.d 0 1) (by simp) with h3314 | h3314
                      · rcases p3081_3 (m.d 1 2) (by simp) with h3315 | h3315
                        · linarith only [h2879, h3315, hlam]
                        · rcases p3081_3 (m.d 1 3) (by simp) with h3317 | h3317
                          · linarith only [h2882, h3317, hlam]
                          · linarith only [h2202, h3317, hlam]
                      · linarith only [h0, h3314, hlam]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [h2881, h3, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3081_1]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      rcases p3081_3 (m.d 0 1) (by simp) with h3322 | h3322
                      · rcases p3081_3 (m.d 1 2) (by simp) with h3323 | h3323
                        · linarith only [h2879, h3323, hlam]
                        · rcases p3081_3 (m.d 1 3) (by simp) with h3325 | h3325
                          · linarith only [h2882, h3325, hlam]
                          · linarith only [h2881, h3325, hlam]
                      · linarith only [h2, h3322, hlam]
                    · have p3081_0 := h3081c.1
                      have p3081_1 := h3081c.2.1
                      have p3081_2 := h3081c.2.2.1
                      have p3081_3 := h3081c.2.2.2
                      linarith only [hlam, p3081_0]
            · linarith only [h1, h2202, h2881, h3074, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
      · rcases m.htr 1 3 5 (by decide) (by decide) with h3331 | h3331
        · linarith only [h2881, h3331, h7, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3333 | h3333
          · linarith only [h2, h3333, h9, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3335 | h3335
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3336 | h3336
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3337 | h3337
                · linarith only [h3337, h5, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3339 | h3339
                  · linarith only [h3335, h3339, h5, h9, hlam]
                  · rcases h1bigk with h3341c | h3341c | h3341c | h3341c | h3341c | h3341c | h3341c | h3341c | h3341c | h3341c | h3341c | h3341c | h3341c | h3341c | h3341c | h3341c | h3341c | h3341c | h3341c | h3341c | h3341c | h3341c | h3341c | h3341c | h3341c
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [hlam, p3341_0]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [h0, h2202, h2881, h3336, h3339, h4, hlam, p3341_2]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [h0, h2881, h3336, h3339, h4, hlam, p3341_2]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      rcases p3341_3 (m.d 0 1) (by simp) with h3345 | h3345
                      · rcases p3341_3 (m.d 1 2) (by simp) with h3346 | h3346
                        · linarith only [h0, h3346, hlam]
                        · rcases p3341_3 (m.d 1 3) (by simp) with h3348 | h3348
                          · linarith only [h1, h3348, hlam]
                          · rcases p3341_3 (m.d 1 4) (by simp) with h3350 | h3350
                            · linarith only [h3350, hlam, p3341_0]
                            · rcases p3341_3 (m.d 1 5) (by simp) with h3352 | h3352
                              · linarith only [h3, h3352, hlam]
                              · linarith only [h3333, h3352, hlam]
                      · linarith only [h3345, hlam, p3341_0]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      rcases p3341_3 (m.d 0 1) (by simp) with h3356 | h3356
                      · rcases p3341_3 (m.d 1 2) (by simp) with h3357 | h3357
                        · linarith only [h0, h3357, hlam]
                        · rcases p3341_3 (m.d 1 3) (by simp) with h3359 | h3359
                          · linarith only [h1, h3359, hlam]
                          · rcases p3341_3 (m.d 1 4) (by simp) with h3361 | h3361
                            · linarith only [h2, h3361, hlam]
                            · rcases p3341_3 (m.d 1 5) (by simp) with h3363 | h3363
                              · linarith only [h3363, hlam, p3341_0]
                              · rcases h1emax with h3365 | h3365 | h3365 | h3365 | h3365
                                · linarith only [h0, h2202, h2881, h3336, h3339, h3365, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                · rcases h3bigk with h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    rcases p3367_3 (m.d 0 3) (by simp) with h3369 | h3369
                                    · rcases p3367_3 (m.d 1 3) (by simp) with h3370 | h3370
                                      · linarith only [h1, h3370, hlam]
                                      · rcases p3367_3 (m.d 2 3) (by simp) with h3372 | h3372
                                        · linarith only [h3372, h4, hlam]
                                        · linarith only [h2202, h3372, hlam]
                                    · linarith only [h1, h3369, hlam]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h2202, h2881, h3336, h3339, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    rcases p3367_3 (m.d 0 3) (by simp) with h3377 | h3377
                                    · rcases p3367_3 (m.d 1 3) (by simp) with h3378 | h3378
                                      · linarith only [h1, h3378, hlam]
                                      · rcases p3367_3 (m.d 2 3) (by simp) with h3380 | h3380
                                        · linarith only [h3380, h4, hlam]
                                        · linarith only [h3335, h3380, hlam]
                                    · linarith only [h3377, hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    rcases p3367_3 (m.d 0 3) (by simp) with h3384 | h3384
                                    · rcases p3367_3 (m.d 1 3) (by simp) with h3385 | h3385
                                      · linarith only [h1, h3385, hlam]
                                      · rcases p3367_3 (m.d 2 3) (by simp) with h3387 | h3387
                                        · linarith only [h3387, h4, hlam]
                                        · linarith only [h3336, h3387, hlam]
                                    · linarith only [h3384, hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h1, hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h2202, hlam, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h2881, hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h3331, hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h4, hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    rcases p3367_3 (m.d 0 3) (by simp) with h3397 | h3397
                                    · rcases p3367_3 (m.d 1 3) (by simp) with h3398 | h3398
                                      · linarith only [h2202, h3398, hlam]
                                      · rcases p3367_3 (m.d 2 3) (by simp) with h3400 | h3400
                                        · rcases p3367_3 (m.d 3 4) (by simp) with h3401 | h3401
                                          · linarith only [h3335, h3401, hlam]
                                          · linarith only [h2881, h3401, hlam]
                                        · linarith only [h2202, h3400, hlam]
                                    · linarith only [h1, h3397, hlam]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h0, h2202, h2881, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h0, h2202, h2881, h3339, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h7, hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h2202, h3335, h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h3335, hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h3339, hlam, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h8, hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h0, h2202, h3336, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h3336, hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h0, h3336, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [hlam, p3367_0]
                                · rcases h3bigk with h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c | h3419c
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [hlam, p3419_0]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    rcases p3419_3 (m.d 0 3) (by simp) with h3421 | h3421
                                    · rcases p3419_3 (m.d 1 3) (by simp) with h3422 | h3422
                                      · linarith only [h1, h3422, hlam]
                                      · rcases p3419_3 (m.d 2 3) (by simp) with h3424 | h3424
                                        · linarith only [h3424, h4, hlam]
                                        · linarith only [h2202, h3424, hlam]
                                    · linarith only [h1, h3421, hlam]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [h3331, h3336, hc03, hlam, hphi, ht0b, ht5b, p3419_1, u5ehi1]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    rcases p3419_3 (m.d 0 3) (by simp) with h3429 | h3429
                                    · rcases p3419_3 (m.d 1 3) (by simp) with h3430 | h3430
                                      · linarith only [h1, h3430, hlam]
                                      · rcases p3419_3 (m.d 2 3) (by simp) with h3432 | h3432
                                        · linarith only [h3432, h4, hlam]
                                        · linarith only [h3335, h3432, hlam]
                                    · linarith only [h3429, hlam, p3419_0]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    rcases p3419_3 (m.d 0 3) (by simp) with h3436 | h3436
                                    · rcases p3419_3 (m.d 1 3) (by simp) with h3437 | h3437
                                      · linarith only [h1, h3437, hlam]
                                      · rcases p3419_3 (m.d 2 3) (by simp) with h3439 | h3439
                                        · linarith only [h3439, h4, hlam]
                                        · linarith only [h3336, h3439, hlam]
                                    · linarith only [h3436, hlam, p3419_0]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [h1, hlam, p3419_0]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [hlam, p3419_0]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [h2202, hlam, p3419_1]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [h2881, hlam, p3419_0]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [h3331, hlam, p3419_0]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [h4, hlam, p3419_0]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    rcases p3419_3 (m.d 0 3) (by simp) with h3449 | h3449
                                    · rcases p3419_3 (m.d 1 3) (by simp) with h3450 | h3450
                                      · linarith only [h2202, h3450, hlam]
                                      · rcases p3419_3 (m.d 2 3) (by simp) with h3452 | h3452
                                        · rcases p3419_3 (m.d 3 4) (by simp) with h3453 | h3453
                                          · linarith only [h3335, h3453, hlam]
                                          · linarith only [h2881, h3453, hlam]
                                        · linarith only [h2202, h3452, hlam]
                                    · linarith only [h1, h3449, hlam]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [hlam, p3419_0]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [h2202, h2881, hc12, hc23, hlam, hphi, p3419_1]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [h0, h2202, h2881, h3339, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3419_1]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [h7, hlam, p3419_0]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [h2202, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34, p3419_1]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [h3335, hlam, p3419_0]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [hlam, p3419_0]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [h3339, hlam, p3419_1]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [h8, hlam, p3419_0]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [h0, h2202, h3336, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3419_1]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [h3336, hlam, p3419_0]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [h0, h3336, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3419_1]
                                  · have p3419_0 := h3419c.1
                                    have p3419_1 := h3419c.2.1
                                    have p3419_2 := h3419c.2.2.1
                                    have p3419_3 := h3419c.2.2.2
                                    linarith only [hlam, p3419_0]
                                · rcases h3bigk with h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c | h3471c
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [hlam, p3471_0]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    rcases p3471_3 (m.d 0 3) (by simp) with h3473 | h3473
                                    · rcases p3471_3 (m.d 1 3) (by simp) with h3474 | h3474
                                      · linarith only [h1, h3474, hlam]
                                      · rcases p3471_3 (m.d 2 3) (by simp) with h3476 | h3476
                                        · linarith only [h3476, h4, hlam]
                                        · linarith only [h2202, h3476, hlam]
                                    · linarith only [h1, h3473, hlam]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [h3336, hc03, hlam, hphi, ht0b, ht5b, p3471_1, u5ehi3]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    rcases p3471_3 (m.d 0 3) (by simp) with h3481 | h3481
                                    · rcases p3471_3 (m.d 1 3) (by simp) with h3482 | h3482
                                      · linarith only [h1, h3482, hlam]
                                      · rcases p3471_3 (m.d 2 3) (by simp) with h3484 | h3484
                                        · linarith only [h3484, h4, hlam]
                                        · linarith only [h3335, h3484, hlam]
                                    · linarith only [h3481, hlam, p3471_0]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    rcases p3471_3 (m.d 0 3) (by simp) with h3488 | h3488
                                    · rcases p3471_3 (m.d 1 3) (by simp) with h3489 | h3489
                                      · linarith only [h1, h3489, hlam]
                                      · rcases p3471_3 (m.d 2 3) (by simp) with h3491 | h3491
                                        · linarith only [h3491, h4, hlam]
                                        · linarith only [h3336, h3491, hlam]
                                    · linarith only [h3488, hlam, p3471_0]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [h1, hlam, p3471_0]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [hlam, p3471_0]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [h2202, hlam, p3471_1]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [h2881, hlam, p3471_0]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [h3331, hlam, p3471_0]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [h4, hlam, p3471_0]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    rcases p3471_3 (m.d 0 3) (by simp) with h3501 | h3501
                                    · rcases p3471_3 (m.d 1 3) (by simp) with h3502 | h3502
                                      · linarith only [h2202, h3502, hlam]
                                      · rcases p3471_3 (m.d 2 3) (by simp) with h3504 | h3504
                                        · rcases p3471_3 (m.d 3 4) (by simp) with h3505 | h3505
                                          · linarith only [h3335, h3505, hlam]
                                          · linarith only [h2881, h3505, hlam]
                                        · linarith only [h2202, h3504, hlam]
                                    · linarith only [h1, h3501, hlam]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [hlam, p3471_0]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [h2202, h2881, hc12, hc23, hlam, hphi, p3471_1]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [h0, h2202, h2881, h3339, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3471_1]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [h7, hlam, p3471_0]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [h2202, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34, p3471_1]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [h3335, hlam, p3471_0]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [hlam, p3471_0]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [h3339, hlam, p3471_1]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [h8, hlam, p3471_0]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [h0, h2202, h3336, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3471_1]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [h3336, hlam, p3471_0]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [h0, h3336, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3471_1]
                                  · have p3471_0 := h3471c.1
                                    have p3471_1 := h3471c.2.1
                                    have p3471_2 := h3471c.2.2.1
                                    have p3471_3 := h3471c.2.2.2
                                    linarith only [hlam, p3471_0]
                                · rcases h3bigk with h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c | h3523c
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [hlam, p3523_0]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    rcases p3523_3 (m.d 0 3) (by simp) with h3525 | h3525
                                    · rcases p3523_3 (m.d 1 3) (by simp) with h3526 | h3526
                                      · linarith only [h1, h3526, hlam]
                                      · rcases p3523_3 (m.d 2 3) (by simp) with h3528 | h3528
                                        · linarith only [h3528, h4, hlam]
                                        · linarith only [h2202, h3528, hlam]
                                    · linarith only [h1, h3525, hlam]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [h3336, hc03, hlam, hphi, ht0b, ht5b, p3523_1, u5ehi3]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    rcases p3523_3 (m.d 0 3) (by simp) with h3533 | h3533
                                    · rcases p3523_3 (m.d 1 3) (by simp) with h3534 | h3534
                                      · linarith only [h1, h3534, hlam]
                                      · rcases p3523_3 (m.d 2 3) (by simp) with h3536 | h3536
                                        · linarith only [h3536, h4, hlam]
                                        · linarith only [h3335, h3536, hlam]
                                    · linarith only [h3533, hlam, p3523_0]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    rcases p3523_3 (m.d 0 3) (by simp) with h3540 | h3540
                                    · rcases p3523_3 (m.d 1 3) (by simp) with h3541 | h3541
                                      · linarith only [h1, h3541, hlam]
                                      · rcases p3523_3 (m.d 2 3) (by simp) with h3543 | h3543
                                        · linarith only [h3543, h4, hlam]
                                        · linarith only [h3336, h3543, hlam]
                                    · linarith only [h3540, hlam, p3523_0]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [h1, hlam, p3523_0]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [hlam, p3523_0]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [h2202, hlam, p3523_1]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [h2881, hlam, p3523_0]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [h3331, hlam, p3523_0]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [h4, hlam, p3523_0]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    rcases p3523_3 (m.d 0 3) (by simp) with h3553 | h3553
                                    · rcases p3523_3 (m.d 1 3) (by simp) with h3554 | h3554
                                      · linarith only [h2202, h3554, hlam]
                                      · rcases p3523_3 (m.d 2 3) (by simp) with h3556 | h3556
                                        · rcases p3523_3 (m.d 3 4) (by simp) with h3557 | h3557
                                          · linarith only [h3335, h3557, hlam]
                                          · linarith only [h2881, h3557, hlam]
                                        · linarith only [h2202, h3556, hlam]
                                    · linarith only [h1, h3553, hlam]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [hlam, p3523_0]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [h2202, h2881, hc12, hc23, hlam, hphi, p3523_1]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [h0, h2202, h2881, h3339, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3523_1]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [h7, hlam, p3523_0]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [h2202, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34, p3523_1]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [h3335, hlam, p3523_0]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [hlam, p3523_0]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [h3339, hlam, p3523_1]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [h8, hlam, p3523_0]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [h0, h2202, h3336, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3523_1]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [h3336, hlam, p3523_0]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [h0, h3336, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p3523_1]
                                  · have p3523_0 := h3523c.1
                                    have p3523_1 := h3523c.2.1
                                    have p3523_2 := h3523c.2.2.1
                                    have p3523_3 := h3523c.2.2.2
                                    linarith only [hlam, p3523_0]
                      · linarith only [h3356, hlam, p3341_0]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [h0, hlam, p3341_0]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [hlam, p3341_0]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [h2202, hlam, p3341_0]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [h2806, hlam, p3341_0]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [h2879, hlam, p3341_0]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [h1, hlam, p3341_0]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [h2881, hc12, hc34, hlam, hphi, ht23, p3341_1]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [hlam, p3341_0]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [h2881, hlam, p3341_1]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [h3331, hlam, p3341_1]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [h2, hlam, p3341_0]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [h2, h9, hc12, hc45, hlam, hphi, ht23, ht34, p3341_1]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [h2806, h5, h9, hc13, hc45, hlam, hphi, ht34, p3341_1]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [hlam, p3341_0]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [h3333, hlam, p3341_1]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [h3, hlam, p3341_0]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [h0, h3331, h3336, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3341_1]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [h0, h2202, h3331, h3336, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3341_1]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [h0, h3331, h3336, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3341_1]
                    · have p3341_0 := h3341c.1
                      have p3341_1 := h3341c.2.1
                      have p3341_2 := h3341c.2.2.1
                      have p3341_3 := h3341c.2.2.2
                      linarith only [hlam, p3341_0]
              · linarith only [h2202, h2881, h3335, h3336, hc12, hc35, hlam, hphi, ht23]
            · linarith only [h2202, h3335, h7, h9, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 7178000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s8_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 2 3 (by decide) (by decide) with h2202 | h2202
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s8_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2202
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s8_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h2202

set_option maxHeartbeats 7178000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s8 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s8_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s8_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9

end R2N4
