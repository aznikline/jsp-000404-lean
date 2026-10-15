import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_9S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6906000 in
set_option maxHeartbeats 6906000 in
theorem r1l7_13_24_L_I_H_I_s5_x1_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h2647 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 4 5 (by decide) (by decide) with h2857 | h2857
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2858 | h2858
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2859 | h2859
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2860 | h2860
        · linarith only [h1, h2860, h6, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h2862 | h2862
          · linarith only [h1, h2647, h2862, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h2864 | h2864
            · rcases m.htr 2 3 4 (by decide) (by decide) with h2865 | h2865
              · linarith only [h1, h2858, h2865, h6, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h2867 | h2867
                · linarith only [h1, h2647, h2858, h2867, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h2869 | h2869
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2870 | h2870
                    · rcases h3bigk with h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c | h2871c
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        linarith only [hlam, p2871_0]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        linarith only [h2647, h2870, hc13, hc34, hlam, hphi, p2871_1]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        linarith only [h2647, h2870, hc23, hc34, hlam, hphi, p2871_1]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        linarith only [h6, hlam, p2871_0]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        linarith only [h2647, hlam, p2871_0]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        linarith only [h1, hlam, p2871_0]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        linarith only [hlam, p2871_0]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        linarith only [h1, h2647, h2870, hc23, hc34, hlam, hphi, p2871_1]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        linarith only [h2860, hlam, p2871_0]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        linarith only [h2862, hlam, p2871_0]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        linarith only [h4, hlam, p2871_0]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        linarith only [h2858, hlam, p2871_0]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        linarith only [hlam, p2871_0]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        linarith only [h2865, hlam, p2871_0]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        linarith only [h2867, hlam, p2871_0]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        rcases p2871_3 (m.d 0 3) (by simp) with h2887 | h2887
                        · linarith only [h2887, hlam, p2871_0]
                        · rcases p2871_3 (m.d 1 3) (by simp) with h2889 | h2889
                          · linarith only [h2860, h2889, hlam]
                          · rcases p2871_3 (m.d 2 3) (by simp) with h2891 | h2891
                            · linarith only [h2865, h2891, hlam]
                            · rcases p2871_3 (m.d 3 4) (by simp) with h2893 | h2893
                              · rcases p2871_3 (m.d 3 5) (by simp) with h2894 | h2894
                                · linarith only [h2870, h2894, hlam]
                                · linarith only [h2647, h2894, hlam]
                              · linarith only [h2893, hlam, p2871_0]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        rcases p2871_3 (m.d 0 3) (by simp) with h2898 | h2898
                        · linarith only [h2898, h6, hlam]
                        · linarith only [h1, h2898, hlam]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        rcases p2871_3 (m.d 0 3) (by simp) with h2901 | h2901
                        · linarith only [h2901, h6, hlam]
                        · linarith only [h2901, h4, hlam]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        linarith only [hlam, p2871_0]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        linarith only [h2647, hc03, hc34, hlam, hphi, p2871_1]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        rcases p2871_3 (m.d 0 3) (by simp) with h2906 | h2906
                        · linarith only [h2906, hlam, p2871_0]
                        · rcases p2871_3 (m.d 1 3) (by simp) with h2908 | h2908
                          · linarith only [h2862, h2908, hlam]
                          · rcases p2871_3 (m.d 2 3) (by simp) with h2910 | h2910
                            · linarith only [h2867, h2910, hlam]
                            · rcases p2871_3 (m.d 3 4) (by simp) with h2912 | h2912
                              · rcases p2871_3 (m.d 3 5) (by simp) with h2913 | h2913
                                · rcases h4bigk with h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c | h2914c
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [hlam, p2914_0]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [h2859, h2869, hc04, hc45, hlam, hphi, ht0b, ht5b, p2914_1]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [h0, h2869, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p2914_1]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [h6, hlam, p2914_0]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    rcases p2914_3 (m.d 0 4) (by simp) with h2919 | h2919
                                    · rcases p2914_3 (m.d 1 4) (by simp) with h2920 | h2920
                                      · linarith only [h2, h2920, hlam]
                                      · linarith only [h2864, h2920, hlam]
                                    · linarith only [h2919, hlam, p2914_0]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [h2, hlam, p2914_1]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [hlam, p2914_0]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [h2869, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p2914_1]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [h2860, hlam, p2914_1]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [h0, h2859, hc01, hc45, hlam, hphi, ht0b, ht5b, p2914_1]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [h5, hlam, p2914_1]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [h2859, hlam, p2914_1]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [hlam, p2914_0]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [h2865, hlam, p2914_1]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p2914_1]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [h1, h2858, h6, hc23, hc34, hlam, hphi, p2914_1]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [h2858, h2860, hc23, hc34, hlam, hphi, p2914_1]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [h2865, hc23, hc34, hlam, hphi, p2914_1]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [hlam, p2914_0]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    rcases p2914_3 (m.d 0 4) (by simp) with h2938 | h2938
                                    · linarith only [h2938, h6, hlam]
                                    · linarith only [h2857, h2938, hlam]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [h2857, hlam, p2914_0]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [h2864, hlam, p2914_0]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [h2869, hlam, p2914_0]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [h2870, hlam, p2914_0]
                                  · have p2914_0 := h2914c.1
                                    have p2914_1 := h2914c.2.1
                                    have p2914_2 := h2914c.2.2.1
                                    have p2914_3 := h2914c.2.2.2
                                    linarith only [hlam, p2914_0]
                                · linarith only [h2913, hlam, p2871_0]
                              · linarith only [h2912, h6, hlam]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        rcases p2871_3 (m.d 0 3) (by simp) with h2948 | h2948
                        · linarith only [h2647, h2948, hlam]
                        · linarith only [h1, h2948, hlam]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        rcases p2871_3 (m.d 0 3) (by simp) with h2951 | h2951
                        · linarith only [h2647, h2951, hlam]
                        · linarith only [h2951, h4, hlam]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        linarith only [h2870, hlam, p2871_0]
                      · have p2871_0 := h2871c.1
                        have p2871_1 := h2871c.2.1
                        have p2871_2 := h2871c.2.2.1
                        have p2871_3 := h2871c.2.2.2
                        linarith only [hlam, p2871_0]
                    · linarith only [h1, h2, h2858, h2859, h2869, h2870, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h2957 | h2957
                    · rcases h3bigk with h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c | h2958c
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        linarith only [hlam, p2958_0]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        linarith only [h2858, h6, hc23, hc34, hlam, hphi, p2958_1]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        linarith only [h6, hc23, hc34, hlam, hphi, p2958_1]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        linarith only [h6, hlam, p2958_0]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        linarith only [h2647, hlam, p2958_0]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        linarith only [h1, hlam, p2958_0]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        linarith only [hlam, p2958_0]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        linarith only [h1, h6, hc23, hc34, hlam, hphi, p2958_1]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        linarith only [h2860, hlam, p2958_0]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        linarith only [h2862, hlam, p2958_0]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        linarith only [h4, hlam, p2958_0]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        linarith only [h2858, hlam, p2958_0]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        linarith only [hlam, p2958_0]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        linarith only [h2865, hlam, p2958_0]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        linarith only [h2867, hlam, p2958_0]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        rcases p2958_3 (m.d 0 3) (by simp) with h2974 | h2974
                        · linarith only [h2974, hlam, p2958_0]
                        · rcases p2958_3 (m.d 1 3) (by simp) with h2976 | h2976
                          · linarith only [h2860, h2976, hlam]
                          · rcases p2958_3 (m.d 2 3) (by simp) with h2978 | h2978
                            · linarith only [h2865, h2978, hlam]
                            · rcases p2958_3 (m.d 3 4) (by simp) with h2980 | h2980
                              · rcases p2958_3 (m.d 3 5) (by simp) with h2981 | h2981
                                · linarith only [h2957, h2981, hlam]
                                · linarith only [h2647, h2981, hlam]
                              · linarith only [h2980, hlam, p2958_0]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        rcases p2958_3 (m.d 0 3) (by simp) with h2985 | h2985
                        · linarith only [h2985, h6, hlam]
                        · linarith only [h1, h2985, hlam]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        rcases p2958_3 (m.d 0 3) (by simp) with h2988 | h2988
                        · linarith only [h2988, h6, hlam]
                        · linarith only [h2988, h4, hlam]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        linarith only [hlam, p2958_0]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        linarith only [h2647, hc03, hc34, hlam, hphi, p2958_1]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        rcases p2958_3 (m.d 0 3) (by simp) with h2993 | h2993
                        · linarith only [h2993, hlam, p2958_0]
                        · rcases p2958_3 (m.d 1 3) (by simp) with h2995 | h2995
                          · linarith only [h2862, h2995, hlam]
                          · rcases p2958_3 (m.d 2 3) (by simp) with h2997 | h2997
                            · linarith only [h2867, h2997, hlam]
                            · rcases p2958_3 (m.d 3 4) (by simp) with h2999 | h2999
                              · rcases p2958_3 (m.d 3 5) (by simp) with h3000 | h3000
                                · rcases h4bigk with h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c | h3001c
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [hlam, p3001_0]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h2859, h2865, h6, hc23, hc34, hlam, hphi, p3001_1]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h2865, h6, hc23, hc34, hlam, hphi, p3001_1]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h6, hlam, p3001_0]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h2865, h2869, h6, hc23, hc34, hlam, hphi, p3001_1]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h2, hlam, p3001_1]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [hlam, p3001_0]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h2, h2865, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3001_1]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h2860, hlam, p3001_1]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h0, h2859, h2865, h2869, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3001_1]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h5, hlam, p3001_1]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h2859, hlam, p3001_1]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [hlam, p3001_0]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h2865, hlam, p3001_1]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h2869, hlam, p3001_0]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h2865, h5, hc23, hc34, hlam, hphi, p3001_1]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h2859, h2865, hc23, hc34, hlam, hphi, p3001_1]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h2865, hc23, hc34, hlam, hphi, p3001_1]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [hlam, p3001_0]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h2865, h2869, hc23, hc34, hlam, hphi, p3001_1]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h2857, hlam, p3001_0]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h2864, hlam, p3001_0]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h2, h2864, h2865, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3001_1]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [h2957, hlam, p3001_0]
                                  · have p3001_0 := h3001c.1
                                    have p3001_1 := h3001c.2.1
                                    have p3001_2 := h3001c.2.2.1
                                    have p3001_3 := h3001c.2.2.2
                                    linarith only [hlam, p3001_0]
                                · linarith only [h3000, hlam, p2958_0]
                              · linarith only [h2999, h6, hlam]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        rcases p2958_3 (m.d 0 3) (by simp) with h3029 | h3029
                        · linarith only [h2647, h3029, hlam]
                        · linarith only [h1, h3029, hlam]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        rcases p2958_3 (m.d 0 3) (by simp) with h3032 | h3032
                        · linarith only [h2647, h3032, hlam]
                        · linarith only [h3032, h4, hlam]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        linarith only [h2957, hlam, p2958_0]
                      · have p2958_0 := h2958c.1
                        have p2958_1 := h2958c.2.1
                        have p2958_2 := h2958c.2.2.1
                        have p2958_3 := h2958c.2.2.2
                        linarith only [hlam, p2958_0]
                    · linarith only [h2, h2864, h2957, h6, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3038 | h3038
              · linarith only [h1, h2857, h2858, h2864, h3038, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3040 | h3040
                · linarith only [h2647, h2857, h2858, h2860, h2864, h3040, hc03, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3042 | h3042
                  · linarith only [h0, h2859, h2860, h2864, h3042, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3044 | h3044
                    · rcases h3bigk with h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        linarith only [hlam, p3045_0]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        linarith only [h2858, h6, hc23, hc34, hlam, hphi, p3045_1]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        linarith only [h6, hc23, hc34, hlam, hphi, p3045_1]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        linarith only [h6, hlam, p3045_0]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        linarith only [h2647, hlam, p3045_0]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        linarith only [h1, hlam, p3045_0]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        linarith only [hlam, p3045_0]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        linarith only [h2857, h2860, h2864, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3045_1]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        linarith only [h2860, hlam, p3045_0]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        linarith only [h2862, hlam, p3045_0]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        linarith only [h4, hlam, p3045_0]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        linarith only [h2858, hlam, p3045_0]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        linarith only [hlam, p3045_0]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        linarith only [h3038, hlam, p3045_0]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        linarith only [h3040, hlam, p3045_0]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        rcases p3045_3 (m.d 0 3) (by simp) with h3061 | h3061
                        · linarith only [h3061, hlam, p3045_0]
                        · rcases p3045_3 (m.d 1 3) (by simp) with h3063 | h3063
                          · linarith only [h2860, h3063, hlam]
                          · rcases p3045_3 (m.d 2 3) (by simp) with h3065 | h3065
                            · linarith only [h3038, h3065, hlam]
                            · rcases p3045_3 (m.d 3 4) (by simp) with h3067 | h3067
                              · rcases p3045_3 (m.d 3 5) (by simp) with h3068 | h3068
                                · linarith only [h3044, h3068, hlam]
                                · linarith only [h2647, h3068, hlam]
                              · linarith only [h3067, hlam, p3045_0]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        rcases p3045_3 (m.d 0 3) (by simp) with h3072 | h3072
                        · linarith only [h3072, h6, hlam]
                        · linarith only [h1, h3072, hlam]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        rcases p3045_3 (m.d 0 3) (by simp) with h3075 | h3075
                        · linarith only [h3075, h6, hlam]
                        · linarith only [h3075, h4, hlam]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        linarith only [hlam, p3045_0]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        linarith only [h2647, h2857, h2860, h2864, hc13, hc34, hlam, hphi, p3045_1]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        rcases p3045_3 (m.d 0 3) (by simp) with h3080 | h3080
                        · linarith only [h3080, hlam, p3045_0]
                        · rcases p3045_3 (m.d 1 3) (by simp) with h3082 | h3082
                          · linarith only [h2862, h3082, hlam]
                          · rcases p3045_3 (m.d 2 3) (by simp) with h3084 | h3084
                            · linarith only [h3040, h3084, hlam]
                            · rcases p3045_3 (m.d 3 4) (by simp) with h3086 | h3086
                              · rcases p3045_3 (m.d 3 5) (by simp) with h3087 | h3087
                                · rcases h4bigk with h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c | h3088c
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [hlam, p3088_0]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h2858, h2860, h6, hc23, hc34, hlam, hphi, p3088_1]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h3038, h6, hc23, hc34, hlam, hphi, p3088_1]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h6, hlam, p3088_0]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h2858, h2860, h2864, h6, hc23, hc34, hlam, hphi, p3088_1]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h2, hlam, p3088_1]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [hlam, p3088_0]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h2857, h2864, hc05, hc24, hlam, hphi, ht0b, ht45, ht5b, p3088_1]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h2860, hlam, p3088_1]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h2864, hlam, p3088_0]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h5, hlam, p3088_1]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h2859, hlam, p3088_1]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [hlam, p3088_0]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h3038, hlam, p3088_1]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h3042, hlam, p3088_0]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h6, hc03, hc34, hlam, hphi, p3088_1]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h2858, h2860, hc23, hc34, hlam, hphi, p3088_1]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h3038, hc23, hc34, hlam, hphi, p3088_1]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [hlam, p3088_0]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h2858, h2860, h2864, hc23, hc34, hlam, hphi, p3088_1]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h2857, hlam, p3088_0]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h0, h2857, h2858, h2860, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3088_1]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h2857, h3038, h6, hc23, hc34, hlam, hphi, p3088_1]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [h3044, hlam, p3088_0]
                                  · have p3088_0 := h3088c.1
                                    have p3088_1 := h3088c.2.1
                                    have p3088_2 := h3088c.2.2.1
                                    have p3088_3 := h3088c.2.2.2
                                    linarith only [hlam, p3088_0]
                                · linarith only [h3087, hlam, p3045_0]
                              · linarith only [h3086, h6, hlam]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        rcases p3045_3 (m.d 0 3) (by simp) with h3116 | h3116
                        · linarith only [h2647, h3116, hlam]
                        · linarith only [h1, h3116, hlam]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        rcases p3045_3 (m.d 0 3) (by simp) with h3119 | h3119
                        · linarith only [h2647, h3119, hlam]
                        · linarith only [h3119, h4, hlam]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        linarith only [h3044, hlam, p3045_0]
                      · have p3045_0 := h3045c.1
                        have p3045_1 := h3045c.2.1
                        have p3045_2 := h3045c.2.2.1
                        have p3045_3 := h3045c.2.2.2
                        linarith only [hlam, p3045_0]
                    · linarith only [h2857, h3044, h6, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3125 | h3125
        · linarith only [h1, h3125, h6, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h3127 | h3127
          · linarith only [h2647, h2858, h2859, h3127, h5, h6, hc03, hc34, hlam, hphi]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3129 | h3129
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3130 | h3130
              · linarith only [h1, h2858, h3130, h6, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3132 | h3132
                · linarith only [h0, h2647, h2858, h3132, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3134 | h3134
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3135 | h3135
                    · rcases h3bigk with h3136c | h3136c | h3136c | h3136c | h3136c | h3136c | h3136c | h3136c | h3136c | h3136c | h3136c | h3136c | h3136c | h3136c | h3136c | h3136c | h3136c | h3136c | h3136c | h3136c | h3136c | h3136c | h3136c | h3136c | h3136c
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        linarith only [hlam, p3136_0]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        linarith only [h2647, h2858, hc23, hc35, hlam, hphi, p3136_1]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        linarith only [h2647, hc23, hc35, hlam, hphi, p3136_1]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        linarith only [h6, hlam, p3136_0]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        linarith only [h2647, hlam, p3136_0]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        linarith only [h1, hlam, p3136_0]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        linarith only [hlam, p3136_0]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        linarith only [h1, h2647, hc23, hc35, hlam, hphi, p3136_1]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        linarith only [h3125, hlam, p3136_0]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        linarith only [h3127, hlam, p3136_0]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        linarith only [h4, hlam, p3136_0]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        linarith only [h2858, hlam, p3136_0]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        linarith only [hlam, p3136_0]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        linarith only [h3130, hlam, p3136_0]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        linarith only [h3132, hlam, p3136_0]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        rcases p3136_3 (m.d 0 3) (by simp) with h3152 | h3152
                        · linarith only [h3152, hlam, p3136_0]
                        · rcases p3136_3 (m.d 1 3) (by simp) with h3154 | h3154
                          · linarith only [h3125, h3154, hlam]
                          · rcases p3136_3 (m.d 2 3) (by simp) with h3156 | h3156
                            · linarith only [h3130, h3156, hlam]
                            · rcases p3136_3 (m.d 3 4) (by simp) with h3158 | h3158
                              · rcases p3136_3 (m.d 3 5) (by simp) with h3159 | h3159
                                · linarith only [h3135, h3159, hlam]
                                · linarith only [h2647, h3159, hlam]
                              · linarith only [h3158, hlam, p3136_0]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        rcases p3136_3 (m.d 0 3) (by simp) with h3163 | h3163
                        · linarith only [h3163, h6, hlam]
                        · linarith only [h1, h3163, hlam]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        rcases p3136_3 (m.d 0 3) (by simp) with h3166 | h3166
                        · linarith only [h3166, h6, hlam]
                        · linarith only [h3166, h4, hlam]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        linarith only [hlam, p3136_0]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        linarith only [h2647, hc03, hc34, hlam, hphi, p3136_1]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        rcases p3136_3 (m.d 0 3) (by simp) with h3171 | h3171
                        · linarith only [h3171, hlam, p3136_0]
                        · rcases p3136_3 (m.d 1 3) (by simp) with h3173 | h3173
                          · linarith only [h3127, h3173, hlam]
                          · rcases p3136_3 (m.d 2 3) (by simp) with h3175 | h3175
                            · linarith only [h3132, h3175, hlam]
                            · rcases p3136_3 (m.d 3 4) (by simp) with h3177 | h3177
                              · rcases p3136_3 (m.d 3 5) (by simp) with h3178 | h3178
                                · rcases h4bigk with h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c | h3179c
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [hlam, p3179_0]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [h2859, h6, hc12, hc34, hlam, hphi, ht23, p3179_1]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [h2858, h2859, h6, hc23, hc34, hlam, hphi, p3179_1]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [h6, hlam, p3179_0]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    rcases p3179_3 (m.d 0 4) (by simp) with h3184 | h3184
                                    · rcases p3179_3 (m.d 1 4) (by simp) with h3185 | h3185
                                      · linarith only [h2, h3185, hlam]
                                      · linarith only [h3129, h3185, hlam]
                                    · linarith only [h3184, hlam, p3179_0]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [h2, hlam, p3179_1]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [hlam, p3179_0]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [h2859, hlam, p3179_0]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [h3125, hlam, p3179_1]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p3179_1]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [h5, hlam, p3179_1]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [h0, h5, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3179_1]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [hlam, p3179_0]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [h3130, hlam, p3179_1]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [h0, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p3179_1]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [h2, h2858, h2859, hc23, hc34, hlam, hphi, p3179_1]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [h2858, h2859, hc23, hc34, hlam, hphi, p3179_1]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [h2858, h2859, hc23, hc34, hlam, hphi, p3179_1]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [hlam, p3179_0]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    rcases p3179_3 (m.d 0 4) (by simp) with h3203 | h3203
                                    · linarith only [h3203, h6, hlam]
                                    · linarith only [h2857, h3203, hlam]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [h2857, hlam, p3179_0]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [h3129, hlam, p3179_0]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [h3134, hlam, p3179_0]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [h3135, hlam, p3179_0]
                                  · have p3179_0 := h3179c.1
                                    have p3179_1 := h3179c.2.1
                                    have p3179_2 := h3179c.2.2.1
                                    have p3179_3 := h3179c.2.2.2
                                    linarith only [hlam, p3179_0]
                                · linarith only [h3178, hlam, p3136_0]
                              · linarith only [h3177, h6, hlam]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        rcases p3136_3 (m.d 0 3) (by simp) with h3213 | h3213
                        · linarith only [h2647, h3213, hlam]
                        · linarith only [h1, h3213, hlam]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        rcases p3136_3 (m.d 0 3) (by simp) with h3216 | h3216
                        · linarith only [h2647, h3216, hlam]
                        · linarith only [h3216, h4, hlam]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        linarith only [h3135, hlam, p3136_0]
                      · have p3136_0 := h3136c.1
                        have p3136_1 := h3136c.2.1
                        have p3136_2 := h3136c.2.2.1
                        have p3136_3 := h3136c.2.2.2
                        linarith only [hlam, p3136_0]
                    · linarith only [h2858, h2859, h3135, h5, h6, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h2858, h2859, h3129, h3134, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · linarith only [h2857, h2858, h2859, h3129, h6, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3224 | h3224
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3225 | h3225
        · linarith only [h1, h3225, h6, hlam]
        · linarith only [h2858, h3224, h3225, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3228 | h3228
        · linarith only [h1, h2858, h3228, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h3230 | h3230
          · linarith only [h1, h2647, h3230, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3232 | h3232
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3233 | h3233
              · linarith only [h3233, h4, h6, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3235 | h3235
                · linarith only [h2647, h3235, h4, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3237 | h3237
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3238 | h3238
                    · rcases h3bigk with h3239c | h3239c | h3239c | h3239c | h3239c | h3239c | h3239c | h3239c | h3239c | h3239c | h3239c | h3239c | h3239c | h3239c | h3239c | h3239c | h3239c | h3239c | h3239c | h3239c | h3239c | h3239c | h3239c | h3239c | h3239c
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [hlam, p3239_0]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [h2647, h3238, hc13, hc34, hlam, hphi, p3239_1]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [h2647, h3238, hc23, hc34, hlam, hphi, p3239_1]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [h6, hlam, p3239_0]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [h2647, hlam, p3239_0]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [h1, hlam, p3239_0]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [hlam, p3239_0]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [h2858, hlam, p3239_1]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [h3228, hlam, p3239_0]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [h3230, hlam, p3239_0]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [h4, hlam, p3239_0]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [h2647, h3238, h4, hc13, hc34, hlam, hphi, p3239_1]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [hlam, p3239_0]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [h3233, hlam, p3239_0]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [h3235, hlam, p3239_0]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [h2858, h4, hc12, hc34, hlam, hphi, ht23, p3239_1]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        rcases p3239_3 (m.d 0 3) (by simp) with h3256 | h3256
                        · linarith only [h3256, h6, hlam]
                        · linarith only [h1, h3256, hlam]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [h2858, hc12, hc34, hlam, hphi, ht23, p3239_1]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [hlam, p3239_0]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [h2647, h2858, h4, hc12, hc34, hlam, hphi, ht23, p3239_1]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [h2858, h4, hc12, hc35, hlam, hphi, ht23, p3239_1]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        rcases p3239_3 (m.d 0 3) (by simp) with h3263 | h3263
                        · linarith only [h2647, h3263, hlam]
                        · linarith only [h1, h3263, hlam]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [h2858, h3238, hc12, hc34, hlam, hphi, ht23, p3239_1]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [h3238, hlam, p3239_0]
                      · have p3239_0 := h3239c.1
                        have p3239_1 := h3239c.2.1
                        have p3239_2 := h3239c.2.2.1
                        have p3239_3 := h3239c.2.2.2
                        linarith only [hlam, p3239_0]
                    · linarith only [h2858, h3238, h4, h6, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h3224, h3232, h3237, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3271 | h3271
              · linarith only [h2857, h2858, h3228, h3232, h3271, h6, hc12, hc23, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3273 | h3273
                · linarith only [h2647, h3273, h4, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3275 | h3275
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3276 | h3276
                    · rcases h3bigk with h3277c | h3277c | h3277c | h3277c | h3277c | h3277c | h3277c | h3277c | h3277c | h3277c | h3277c | h3277c | h3277c | h3277c | h3277c | h3277c | h3277c | h3277c | h3277c | h3277c | h3277c | h3277c | h3277c | h3277c | h3277c
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [hlam, p3277_0]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [h2647, h2858, h3276, hc12, hc34, hlam, hphi, ht23, p3277_1]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [h2647, h3276, hc23, hc34, hlam, hphi, p3277_1]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [h6, hlam, p3277_0]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [h2647, hlam, p3277_0]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [h1, hlam, p3277_0]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [hlam, p3277_0]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [h2858, hlam, p3277_1]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [h3228, hlam, p3277_0]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [h3230, hlam, p3277_0]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [h4, hlam, p3277_0]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [h2647, h2858, h3276, h4, hc12, hc34, hlam, hphi, ht23, p3277_1]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [hlam, p3277_0]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [h3271, hlam, p3277_0]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [h3273, hlam, p3277_0]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [h2858, h4, hc12, hc34, hlam, hphi, ht23, p3277_1]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        rcases p3277_3 (m.d 0 3) (by simp) with h3294 | h3294
                        · linarith only [h3294, h6, hlam]
                        · linarith only [h1, h3294, hlam]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [h2858, hc12, hc34, hlam, hphi, ht23, p3277_1]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [hlam, p3277_0]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [h2647, h2858, h4, hc12, hc34, hlam, hphi, ht23, p3277_1]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [h2858, h4, hc12, hc35, hlam, hphi, ht23, p3277_1]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        rcases p3277_3 (m.d 0 3) (by simp) with h3301 | h3301
                        · linarith only [h2647, h3301, hlam]
                        · linarith only [h1, h3301, hlam]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [h2858, h3276, hc12, hc34, hlam, hphi, ht23, p3277_1]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [h3276, hlam, p3277_0]
                      · have p3277_0 := h3277c.1
                        have p3277_1 := h3277c.2.1
                        have p3277_2 := h3277c.2.2.1
                        have p3277_3 := h3277c.2.2.2
                        linarith only [hlam, p3277_0]
                    · linarith only [h2858, h3275, h3276, h4, h5, h6, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                  · linarith only [h2857, h3224, h3275, h6, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h3309 | h3309
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3310 | h3310
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3311 | h3311
        · linarith only [h1, h3311, h6, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h3313 | h3313
          · linarith only [h1, h2647, h3313, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3315 | h3315
            · linarith only [h2, h2857, h3315, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3317 | h3317
              · linarith only [h1, h3309, h3317, h6, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3319 | h3319
                · linarith only [h1, h2647, h3309, h3319, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3321 | h3321
                  · linarith only [h0, h2857, h3310, h3321, h6, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3323 | h3323
                    · rcases h3bigk with h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c | h3324c
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        linarith only [hlam, p3324_0]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        linarith only [h2857, h3309, h3323, h6, hc23, hc34, hlam, hphi, p3324_1]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        linarith only [h2857, h3323, h6, hc23, hc34, hlam, hphi, p3324_1]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        linarith only [h6, hlam, p3324_0]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        linarith only [h2647, hlam, p3324_0]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        linarith only [h1, hlam, p3324_0]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        linarith only [hlam, p3324_0]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        linarith only [h1, h2857, h3323, h6, hc23, hc34, hlam, hphi, p3324_1]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        linarith only [h3311, hlam, p3324_0]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        linarith only [h3313, hlam, p3324_0]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        linarith only [h4, hlam, p3324_0]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        linarith only [h3309, hlam, p3324_0]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        linarith only [hlam, p3324_0]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        linarith only [h3317, hlam, p3324_0]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        linarith only [h3319, hlam, p3324_0]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        rcases p3324_3 (m.d 0 3) (by simp) with h3340 | h3340
                        · linarith only [h3340, hlam, p3324_0]
                        · rcases p3324_3 (m.d 1 3) (by simp) with h3342 | h3342
                          · linarith only [h3311, h3342, hlam]
                          · rcases p3324_3 (m.d 2 3) (by simp) with h3344 | h3344
                            · linarith only [h3317, h3344, hlam]
                            · rcases p3324_3 (m.d 3 4) (by simp) with h3346 | h3346
                              · rcases p3324_3 (m.d 3 5) (by simp) with h3347 | h3347
                                · linarith only [h3323, h3347, hlam]
                                · linarith only [h2647, h3347, hlam]
                              · linarith only [h3346, hlam, p3324_0]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        rcases p3324_3 (m.d 0 3) (by simp) with h3351 | h3351
                        · linarith only [h3351, h6, hlam]
                        · linarith only [h1, h3351, hlam]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        rcases p3324_3 (m.d 0 3) (by simp) with h3354 | h3354
                        · linarith only [h3354, h6, hlam]
                        · linarith only [h3354, h4, hlam]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        linarith only [hlam, p3324_0]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        linarith only [h2857, h3323, h6, hc03, hc34, hlam, hphi, p3324_1]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        rcases p3324_3 (m.d 0 3) (by simp) with h3359 | h3359
                        · linarith only [h3359, hlam, p3324_0]
                        · rcases p3324_3 (m.d 1 3) (by simp) with h3361 | h3361
                          · linarith only [h3313, h3361, hlam]
                          · rcases p3324_3 (m.d 2 3) (by simp) with h3363 | h3363
                            · linarith only [h3319, h3363, hlam]
                            · rcases p3324_3 (m.d 3 4) (by simp) with h3365 | h3365
                              · rcases p3324_3 (m.d 3 5) (by simp) with h3366 | h3366
                                · rcases h4bigk with h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c | h3367c
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h2857, h3310, h3323, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h2857, h3323, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h6, hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h2857, hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h2, hlam, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h2, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h3311, hlam, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h3315, hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h5, hlam, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h3310, hlam, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h3317, hlam, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h3321, hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h1, h3309, h6, hc23, hc34, hlam, hphi, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h3309, h3311, hc23, hc34, hlam, hphi, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h3317, hc23, hc34, hlam, hphi, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h1, h2647, h2857, h3309, hc23, hc34, hlam, hphi, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h1, h3309, h6, hc23, hc45, hlam, hphi, ht34, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h3309, h3311, hc23, hc45, hlam, hphi, ht34, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h3317, hc23, hc45, hlam, hphi, ht34, p3367_1]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [h3323, hlam, p3367_0]
                                  · have p3367_0 := h3367c.1
                                    have p3367_1 := h3367c.2.1
                                    have p3367_2 := h3367c.2.2.1
                                    have p3367_3 := h3367c.2.2.2
                                    linarith only [hlam, p3367_0]
                                · linarith only [h3366, hlam, p3324_0]
                              · linarith only [h3365, h6, hlam]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        rcases p3324_3 (m.d 0 3) (by simp) with h3395 | h3395
                        · linarith only [h2647, h3395, hlam]
                        · linarith only [h1, h3395, hlam]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        rcases p3324_3 (m.d 0 3) (by simp) with h3398 | h3398
                        · linarith only [h2647, h3398, hlam]
                        · linarith only [h3398, h4, hlam]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        linarith only [h3323, hlam, p3324_0]
                      · have p3324_0 := h3324c.1
                        have p3324_1 := h3324c.2.1
                        have p3324_2 := h3324c.2.2.1
                        have p3324_3 := h3324c.2.2.2
                        linarith only [hlam, p3324_0]
                    · rcases h3bigk with h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c | h3403c
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [hlam, p3403_0]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [h3309, h6, hc23, hc34, hlam, hphi, p3403_1]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [h3323, h6, hc23, hc45, hlam, hphi, ht34, p3403_1]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [h6, hlam, p3403_0]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [h2647, hlam, p3403_0]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [h1, hlam, p3403_0]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [hlam, p3403_0]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [h1, h3323, h6, hc23, hc45, hlam, hphi, ht34, p3403_1]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [h3311, hlam, p3403_0]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [h3313, hlam, p3403_0]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [h4, hlam, p3403_0]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [h3309, hlam, p3403_0]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [hlam, p3403_0]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [h3317, hlam, p3403_0]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [h3319, hlam, p3403_0]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [h3323, hc03, hc45, hlam, hphi, ht34, p3403_1]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [h3309, h3323, hc23, hc45, hlam, hphi, ht34, p3403_1]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [h3323, hc23, hc45, hlam, hphi, ht34, p3403_1]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [hlam, p3403_0]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [h3323, hlam, p3403_1]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        rcases p3403_3 (m.d 0 3) (by simp) with h3424 | h3424
                        · linarith only [h3424, hlam, p3403_0]
                        · rcases p3403_3 (m.d 1 3) (by simp) with h3426 | h3426
                          · linarith only [h3313, h3426, hlam]
                          · rcases p3403_3 (m.d 2 3) (by simp) with h3428 | h3428
                            · linarith only [h3319, h3428, hlam]
                            · rcases p3403_3 (m.d 3 4) (by simp) with h3430 | h3430
                              · linarith only [h3323, h3430, hlam]
                              · linarith only [h3430, h6, hlam]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        rcases p3403_3 (m.d 0 3) (by simp) with h3433 | h3433
                        · linarith only [h2647, h3433, hlam]
                        · linarith only [h1, h3433, hlam]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        rcases p3403_3 (m.d 0 3) (by simp) with h3436 | h3436
                        · linarith only [h2647, h3436, hlam]
                        · linarith only [h3436, h4, hlam]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [h1, h3309, h3323, h6, hc23, hc45, hlam, hphi, ht34, p3403_1]
                      · have p3403_0 := h3403c.1
                        have p3403_1 := h3403c.2.1
                        have p3403_2 := h3403c.2.2.1
                        have p3403_3 := h3403c.2.2.2
                        linarith only [hlam, p3403_0]
      · linarith only [h2857, h3309, h3310, h5, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3442 | h3442
      · linarith only [h2857, h3309, h3442, h4, h6, hc24, hc45, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3444 | h3444
        · linarith only [h3309, h3444, h4, h6, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h3446 | h3446
          · linarith only [h2647, h3309, h3446, h4, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h3448 | h3448
            · linarith only [h2857, h3442, h3448, h5, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h3450 | h3450
              · linarith only [h3450, h4, h6, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h3452 | h3452
                · linarith only [h2647, h3452, h4, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h3454 | h3454
                  · linarith only [h2857, h3454, h5, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h3456 | h3456
                    · linarith only [h2857, h3309, h3456, h4, h6, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h3309, h3456, h4, h6, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6906000 in
set_option maxHeartbeats 6906000 in
theorem r1l7_13_24_L_I_H_I_s5_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 3 5 (by decide) (by decide) with h2647 | h2647
  · exact r1l7_13_24_L_I_H_I_s5_x1_x0 m hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6 h2647
  · exact r1l7_13_24_L_I_H_I_s5_x1_x1 m hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6 h2647

set_option maxHeartbeats 6906000 in
set_option maxHeartbeats 6906000 in
theorem r1l7_13_24_L_I_H_I_s5 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
  · exact r1l7_13_24_L_I_H_I_s5_x0 m hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6
  · exact r1l7_13_24_L_I_H_I_s5_x1 m hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 h6

end R2N4
