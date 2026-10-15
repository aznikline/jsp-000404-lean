import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9682000 in
set_option maxHeartbeats 9682000 in
theorem r1l7_10_12_25_L_0_L_I_H_I_s1_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_0 m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h2858 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h2859 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h2860 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h2861 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h2862 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0elo := hb0.1
  have h2bigk := hb2.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 4 5 (by decide) (by decide) with h2863 | h2863
  · rcases m.htr 1 2 3 (by decide) (by decide) with h2864 | h2864
    · rcases m.htr 1 2 4 (by decide) (by decide) with h2865 | h2865
      · rcases m.htr 1 2 5 (by decide) (by decide) with h2866 | h2866
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2867 | h2867
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2868 | h2868
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2869 | h2869
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2870 | h2870
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2871 | h2871
                  · linarith only [h2859, h2868, h2871, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                  · linarith only [h2859, h2868, h2870, h2871, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2874 | h2874
                  · linarith only [h2868, h2870, h2874, hlam]
                  · rcases h2bigk with h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c | h2876c
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [hlam, p2876_0]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [h0, hlam, p2876_1]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [h2868, hc34, hlam, hphi, ht0b, ht45, ht5b, p2876_1, u0elo1]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      rcases p2876_3 (m.d 0 2) (by simp) with h2880 | h2880
                      · rcases p2876_3 (m.d 1 2) (by simp) with h2881 | h2881
                        · rcases p2876_3 (m.d 2 3) (by simp) with h2882 | h2882
                          · linarith only [h2859, h2882, hlam]
                          · linarith only [h2868, h2882, hlam]
                        · linarith only [h2865, h2881, hlam]
                      · linarith only [h2880, hlam, p2876_0]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      rcases p2876_3 (m.d 0 2) (by simp) with h2887 | h2887
                      · rcases p2876_3 (m.d 1 2) (by simp) with h2888 | h2888
                        · rcases p2876_3 (m.d 2 3) (by simp) with h2889 | h2889
                          · linarith only [h2859, h2889, hlam]
                          · linarith only [h2869, h2889, hlam]
                        · linarith only [h2866, h2888, hlam]
                      · linarith only [h2887, hlam, p2876_0]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [h0, h2858, h2867, h2868, h2870, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2876_1]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [hlam, p2876_0]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      rcases p2876_3 (m.d 0 2) (by simp) with h2896 | h2896
                      · linarith only [h0, h2896, hlam]
                      · linarith only [h2859, h2896, hlam]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [h0, h2858, h2867, h2870, hlam, p2876_2]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      rcases p2876_3 (m.d 0 2) (by simp) with h2900 | h2900
                      · linarith only [h0, h2900, hlam]
                      · linarith only [h2861, h2900, hlam]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [h2859, hlam, p2876_0]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [h2864, hlam, p2876_0]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [hlam, p2876_0]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [h2859, h2868, hc34, hlam, hphi, ht0b, ht45, ht5b, p2876_1, u0elo1]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [h2859, hc25, hlam, hphi, ht0b, ht5b, p2876_1, u0elo1]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [h2860, hlam, p2876_0]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [h2865, hlam, p2876_0]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [h2868, hlam, p2876_1]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [hlam, p2876_0]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [h2870, hlam, p2876_1]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [h2861, hlam, p2876_0]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [h2866, hlam, p2876_0]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [h2869, hlam, p2876_1]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [h2861, h2868, hc34, hlam, hphi, ht0b, ht45, ht5b, p2876_1, u0elo1]
                    · have p2876_0 := h2876c.1
                      have p2876_1 := h2876c.2.1
                      have p2876_2 := h2876c.2.2.1
                      have p2876_3 := h2876c.2.2.2
                      linarith only [hlam, p2876_0]
              · linarith only [h2859, h2862, h2868, h2869, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2919 | h2919
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2920 | h2920
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2921 | h2921
                  · rcases h2bigk with h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c | h2922c
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [hlam, p2922_0]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [h0, hlam, p2922_1]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [h2919, hc35, hlam, hphi, ht0b, ht5b, p2922_1, u0elo1]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [h2868, h2919, h2921, hc45, hlam, hphi, ht0b, ht5b, p2922_1, u0elo1]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      rcases p2922_3 (m.d 0 2) (by simp) with h2927 | h2927
                      · rcases p2922_3 (m.d 1 2) (by simp) with h2928 | h2928
                        · rcases p2922_3 (m.d 2 3) (by simp) with h2929 | h2929
                          · linarith only [h2859, h2929, hlam]
                          · linarith only [h2919, h2929, hlam]
                        · linarith only [h2866, h2928, hlam]
                      · linarith only [h2927, hlam, p2922_0]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [h2859, h2919, h2921, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2922_1]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [hlam, p2922_0]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      rcases p2922_3 (m.d 0 2) (by simp) with h2936 | h2936
                      · linarith only [h0, h2936, hlam]
                      · linarith only [h2859, h2936, hlam]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      rcases p2922_3 (m.d 0 2) (by simp) with h2939 | h2939
                      · linarith only [h0, h2939, hlam]
                      · linarith only [h2860, h2939, hlam]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      rcases p2922_3 (m.d 0 2) (by simp) with h2942 | h2942
                      · linarith only [h0, h2942, hlam]
                      · linarith only [h2861, h2942, hlam]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [h2859, hlam, p2922_0]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [h2864, hlam, p2922_0]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [hlam, p2922_0]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [h2868, hlam, p2922_0]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [h2860, h2868, h2919, h2921, hc45, hlam, hphi, ht0b, ht5b, p2922_1, u0elo1]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [h2860, hlam, p2922_0]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [h2865, hlam, p2922_0]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [h2860, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2922_1, u0elo1]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [hlam, p2922_0]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [h2860, h2919, h2921, hc45, hlam, hphi, ht0b, ht5b, p2922_1, u0elo1]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [h2861, hlam, p2922_0]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [h2866, hlam, p2922_0]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [h2919, hlam, p2922_1]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [h2920, hlam, p2922_0]
                    · have p2922_0 := h2922c.1
                      have p2922_1 := h2922c.2.1
                      have p2922_2 := h2922c.2.2.1
                      have p2922_3 := h2922c.2.2.2
                      linarith only [hlam, p2922_0]
                  · linarith only [h2863, h2868, h2921, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                · linarith only [h2858, h2867, h2868, h2919, h2920, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2962 | h2962
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2963 | h2963
                  · rcases h2bigk with h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c | h2964c
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [hlam, p2964_0]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [h0, hlam, p2964_1]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      rcases p2964_3 (m.d 0 2) (by simp) with h2967 | h2967
                      · rcases p2964_3 (m.d 1 2) (by simp) with h2968 | h2968
                        · rcases p2964_3 (m.d 2 3) (by simp) with h2969 | h2969
                          · linarith only [h2969, hlam, p2964_0]
                          · rcases p2964_3 (m.d 2 4) (by simp) with h2971 | h2971
                            · linarith only [h2860, h2971, hlam]
                            · linarith only [h2868, h2971, hlam]
                        · linarith only [h2864, h2968, hlam]
                      · linarith only [h2967, hlam, p2964_0]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [h2962, hc45, hlam, hphi, ht0b, ht5b, p2964_1, u0elo1]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      rcases p2964_3 (m.d 0 2) (by simp) with h2977 | h2977
                      · rcases p2964_3 (m.d 1 2) (by simp) with h2978 | h2978
                        · rcases p2964_3 (m.d 2 3) (by simp) with h2979 | h2979
                          · linarith only [h2859, h2979, hlam]
                          · rcases p2964_3 (m.d 2 4) (by simp) with h2981 | h2981
                            · linarith only [h2860, h2981, hlam]
                            · linarith only [h2962, h2981, hlam]
                        · linarith only [h2866, h2978, hlam]
                      · linarith only [h2977, hlam, p2964_0]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [h2860, h2962, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p2964_1]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [hlam, p2964_0]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      rcases p2964_3 (m.d 0 2) (by simp) with h2988 | h2988
                      · linarith only [h0, h2988, hlam]
                      · linarith only [h2859, h2988, hlam]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      rcases p2964_3 (m.d 0 2) (by simp) with h2991 | h2991
                      · linarith only [h0, h2991, hlam]
                      · linarith only [h2860, h2991, hlam]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      rcases p2964_3 (m.d 0 2) (by simp) with h2994 | h2994
                      · linarith only [h0, h2994, hlam]
                      · linarith only [h2861, h2994, hlam]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [h2859, hlam, p2964_0]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [h2864, hlam, p2964_0]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [hlam, p2964_0]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [h2868, hlam, p2964_0]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [h2919, hlam, p2964_0]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [h2860, hlam, p2964_0]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [h2865, hlam, p2964_0]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [h2860, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2964_1, u0elo1]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [hlam, p2964_0]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [h2860, h2919, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2964_1, u0elo1]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [h2861, hlam, p2964_0]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [h2866, hlam, p2964_0]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [h2861, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2964_1, u0elo1]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [h2962, hlam, p2964_0]
                    · have p2964_0 := h2964c.1
                      have p2964_1 := h2964c.2.1
                      have p2964_2 := h2964c.2.2.1
                      have p2964_3 := h2964c.2.2.2
                      linarith only [hlam, p2964_0]
                  · linarith only [h0, h2858, h2867, h2868, h2963, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3013 | h3013
                  · rcases h2bigk with h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c | h3014c
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h0, hlam, p3014_1]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      rcases p3014_3 (m.d 0 2) (by simp) with h3017 | h3017
                      · rcases p3014_3 (m.d 1 2) (by simp) with h3018 | h3018
                        · rcases p3014_3 (m.d 2 3) (by simp) with h3019 | h3019
                          · linarith only [h3019, hlam, p3014_0]
                          · rcases p3014_3 (m.d 2 4) (by simp) with h3021 | h3021
                            · linarith only [h2860, h3021, hlam]
                            · linarith only [h2868, h3021, hlam]
                        · linarith only [h2864, h3018, hlam]
                      · linarith only [h3017, hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      rcases p3014_3 (m.d 0 2) (by simp) with h3026 | h3026
                      · rcases p3014_3 (m.d 1 2) (by simp) with h3027 | h3027
                        · rcases p3014_3 (m.d 2 3) (by simp) with h3028 | h3028
                          · linarith only [h2859, h3028, hlam]
                          · rcases p3014_3 (m.d 2 4) (by simp) with h3030 | h3030
                            · linarith only [h3030, hlam, p3014_0]
                            · rcases p3014_3 (m.d 2 5) (by simp) with h3032 | h3032
                              · linarith only [h2861, h3032, hlam]
                              · linarith only [h2962, h3032, hlam]
                        · linarith only [h2865, h3027, hlam]
                      · linarith only [h3026, hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      rcases p3014_3 (m.d 0 2) (by simp) with h3037 | h3037
                      · rcases p3014_3 (m.d 1 2) (by simp) with h3038 | h3038
                        · rcases p3014_3 (m.d 2 3) (by simp) with h3039 | h3039
                          · linarith only [h2859, h3039, hlam]
                          · rcases p3014_3 (m.d 2 4) (by simp) with h3041 | h3041
                            · linarith only [h2860, h3041, hlam]
                            · rcases p3014_3 (m.d 2 5) (by simp) with h3043 | h3043
                              · linarith only [h3043, hlam, p3014_0]
                              · rcases h5bigk with h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c | h3045c
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [hlam, p3045_0]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [hc15, hlam, hphi, ht0b, ht5b, p3045_1, u0elo4]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [h0, h2858, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3045_1]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [h0, h2858, h3013, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3045_1]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [h0, h2858, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p3045_1]
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
                                  linarith only [h0, h2858, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3045_1]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [h0, h2858, h2962, h3013, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3045_1]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [h0, h2858, h2962, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3045_1]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [h2861, hlam, p3045_1]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [h2866, hlam, p3045_1]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [hlam, p3045_0]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [h2919, hlam, p3045_1]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [h2962, hlam, p3045_1]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [h2862, hlam, p3045_0]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [h2862, hc15, hlam, hphi, ht0b, ht5b, p3045_1, u0elo2]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [h2859, h2862, h2868, h2962, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3045_1, u0elo1]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [hlam, p3045_0]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [h2859, h2862, h2868, h2962, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3045_1, u0elo1]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [h2863, hlam, p3045_0]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [h2867, hlam, p3045_0]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [h2867, h2868, h2962, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3045_1]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [h3013, hlam, p3045_0]
                                · have p3045_0 := h3045c.1
                                  have p3045_1 := h3045c.2.1
                                  have p3045_2 := h3045c.2.2.1
                                  have p3045_3 := h3045c.2.2.2
                                  linarith only [hlam, p3045_0]
                        · linarith only [h2866, h3038, hlam]
                      · linarith only [h3037, hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2859, h2862, h2919, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3014_1]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h0, h2858, h2867, h2868, h2962, hlam, p3014_2]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h0, h2858, h2867, h2962, hlam, p3014_2]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      rcases p3014_3 (m.d 0 2) (by simp) with h3077 | h3077
                      · linarith only [h0, h3077, hlam]
                      · linarith only [h2861, h3077, hlam]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2859, hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2864, hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2868, hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2919, hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2860, hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2865, hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h0, h2858, h2867, h2962, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3014_1]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2962, hlam, p3014_1]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2861, hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2866, hlam, p3014_0]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h2861, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3014_1, u0elo1]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [h0, h2858, h2867, h2962, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3014_1]
                    · have p3014_0 := h3014c.1
                      have p3014_1 := h3014c.2.1
                      have p3014_2 := h3014c.2.2.1
                      have p3014_3 := h3014c.2.2.2
                      linarith only [hlam, p3014_0]
                  · linarith only [h0, h2858, h2867, h2868, h3013, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3096 | h3096
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3097 | h3097
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3098 | h3098
                · linarith only [h2860, h2867, h3098, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3100 | h3100
                  · linarith only [h2865, h2867, h3096, h3100, hlam]
                  · rcases h2bigk with h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c | h3102c
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [hlam, p3102_0]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [h0, hlam, p3102_1]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [h3097, h3100, hc34, hlam, hphi, ht0b, ht45, ht5b, p3102_1, u0elo1]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      rcases p3102_3 (m.d 0 2) (by simp) with h3106 | h3106
                      · rcases p3102_3 (m.d 1 2) (by simp) with h3107 | h3107
                        · rcases p3102_3 (m.d 2 3) (by simp) with h3108 | h3108
                          · linarith only [h2859, h3108, hlam]
                          · linarith only [h3096, h3108, hlam]
                        · linarith only [h2865, h3107, hlam]
                      · linarith only [h3106, hlam, p3102_0]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      rcases p3102_3 (m.d 0 2) (by simp) with h3113 | h3113
                      · rcases p3102_3 (m.d 1 2) (by simp) with h3114 | h3114
                        · rcases p3102_3 (m.d 2 3) (by simp) with h3115 | h3115
                          · linarith only [h2859, h3115, hlam]
                          · linarith only [h3097, h3115, hlam]
                        · linarith only [h2866, h3114, hlam]
                      · linarith only [h3113, hlam, p3102_0]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [h2859, h3097, h3100, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3102_1]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [hlam, p3102_0]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      rcases p3102_3 (m.d 0 2) (by simp) with h3122 | h3122
                      · linarith only [h0, h3122, hlam]
                      · linarith only [h2859, h3122, hlam]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      rcases p3102_3 (m.d 0 2) (by simp) with h3125 | h3125
                      · linarith only [h0, h3125, hlam]
                      · linarith only [h2860, h3125, hlam]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      rcases p3102_3 (m.d 0 2) (by simp) with h3128 | h3128
                      · linarith only [h0, h3128, hlam]
                      · linarith only [h2861, h3128, hlam]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [h2859, hlam, p3102_0]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [h2864, hlam, p3102_0]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [hlam, p3102_0]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [h2859, h3096, hc34, hlam, hphi, ht0b, ht45, ht5b, p3102_1, u0elo1]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [h2859, h3097, h3100, hc34, hlam, hphi, ht0b, ht45, ht5b, p3102_1, u0elo1]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [h2860, hlam, p3102_0]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [h2865, hlam, p3102_0]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [h3096, hlam, p3102_1]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [hlam, p3102_0]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [h3098, hlam, p3102_1]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [h2861, hlam, p3102_0]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [h2866, hlam, p3102_0]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [h3097, hlam, p3102_1]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [h2861, h3096, hc34, hlam, hphi, ht0b, ht45, ht5b, p3102_1, u0elo1]
                    · have p3102_0 := h3102c.1
                      have p3102_1 := h3102c.2.1
                      have p3102_2 := h3102c.2.2.1
                      have p3102_3 := h3102c.2.2.2
                      linarith only [hlam, p3102_0]
              · linarith only [h2859, h2862, h3096, h3097, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3147 | h3147
              · linarith only [h2863, h2865, h2867, h3096, h3147, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3149 | h3149
                · linarith only [h2865, h2867, h3149, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3151 | h3151
                  · rcases h2bigk with h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c | h3152c
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      linarith only [hlam, p3152_0]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      linarith only [h0, hlam, p3152_1]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      rcases p3152_3 (m.d 0 2) (by simp) with h3155 | h3155
                      · rcases p3152_3 (m.d 1 2) (by simp) with h3156 | h3156
                        · rcases p3152_3 (m.d 2 3) (by simp) with h3157 | h3157
                          · linarith only [h3157, hlam, p3152_0]
                          · rcases p3152_3 (m.d 2 4) (by simp) with h3159 | h3159
                            · linarith only [h2860, h3159, hlam]
                            · linarith only [h3096, h3159, hlam]
                        · linarith only [h2864, h3156, hlam]
                      · linarith only [h3155, hlam, p3152_0]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      rcases p3152_3 (m.d 0 2) (by simp) with h3164 | h3164
                      · rcases p3152_3 (m.d 1 2) (by simp) with h3165 | h3165
                        · rcases p3152_3 (m.d 2 3) (by simp) with h3166 | h3166
                          · linarith only [h2859, h3166, hlam]
                          · rcases p3152_3 (m.d 2 4) (by simp) with h3168 | h3168
                            · linarith only [h3168, hlam, p3152_0]
                            · rcases p3152_3 (m.d 2 5) (by simp) with h3170 | h3170
                              · linarith only [h2861, h3170, hlam]
                              · linarith only [h3149, h3170, hlam]
                        · linarith only [h2865, h3165, hlam]
                      · linarith only [h3164, hlam, p3152_0]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      rcases p3152_3 (m.d 0 2) (by simp) with h3175 | h3175
                      · rcases p3152_3 (m.d 1 2) (by simp) with h3176 | h3176
                        · rcases p3152_3 (m.d 2 3) (by simp) with h3177 | h3177
                          · linarith only [h2859, h3177, hlam]
                          · rcases p3152_3 (m.d 2 4) (by simp) with h3179 | h3179
                            · linarith only [h2860, h3179, hlam]
                            · rcases p3152_3 (m.d 2 5) (by simp) with h3181 | h3181
                              · linarith only [h3181, hlam, p3152_0]
                              · rcases h5bigk with h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c | h3183c
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [hlam, p3183_0]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h0, h2858, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h0, h2858, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h0, h2858, h2865, h2867, h3096, h3151, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h0, h2858, h2865, h2867, h3096, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2858, hlam, p3183_0]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [hlam, p3183_0]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h0, h2858, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2867, h3151, hlam, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2867, hlam, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2861, hlam, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2866, hlam, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [hlam, p3183_0]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h3147, hlam, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h3149, hlam, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2862, hlam, p3183_0]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2859, h2862, hc15, hlam, hphi, ht0b, ht5b, p3183_1, u0elo1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2859, h2862, h3096, h3149, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3183_1, u0elo1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [hlam, p3183_0]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2859, h2862, h2865, h2867, h3096, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3183_1, u0elo1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2863, hlam, p3183_0]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2866, h3096, h3149, h3151, hc23, hc34, hlam, hphi, p3183_1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h2860, h2863, h3096, h3149, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3183_1, u0elo1]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [h3151, hlam, p3183_0]
                                · have p3183_0 := h3183c.1
                                  have p3183_1 := h3183c.2.1
                                  have p3183_2 := h3183c.2.2.1
                                  have p3183_3 := h3183c.2.2.2
                                  linarith only [hlam, p3183_0]
                        · linarith only [h2866, h3176, hlam]
                      · linarith only [h3175, hlam, p3152_0]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      linarith only [h2860, h2863, h2865, h2867, h3096, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3152_1]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      linarith only [hlam, p3152_0]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      rcases p3152_3 (m.d 0 2) (by simp) with h3213 | h3213
                      · linarith only [h0, h3213, hlam]
                      · linarith only [h2859, h3213, hlam]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      rcases p3152_3 (m.d 0 2) (by simp) with h3216 | h3216
                      · linarith only [h0, h3216, hlam]
                      · linarith only [h2860, h3216, hlam]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      rcases p3152_3 (m.d 0 2) (by simp) with h3219 | h3219
                      · linarith only [h0, h3219, hlam]
                      · linarith only [h2861, h3219, hlam]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      linarith only [h2859, hlam, p3152_0]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      linarith only [h2864, hlam, p3152_0]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      linarith only [hlam, p3152_0]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      linarith only [h3096, hlam, p3152_0]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      linarith only [h3147, hlam, p3152_0]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      linarith only [h2860, hlam, p3152_0]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      linarith only [h2865, hlam, p3152_0]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      linarith only [h2859, h2862, h2865, h2867, h3151, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3152_1, u0elo1]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      linarith only [hlam, p3152_0]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      linarith only [h3149, hlam, p3152_1]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      linarith only [h2861, hlam, p3152_0]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      linarith only [h2866, hlam, p3152_0]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      linarith only [h2858, h2866, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3152_1, u0elo0]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      linarith only [h2859, h2862, h2866, h2867, h3151, hc24, hlam, hphi, ht0b, ht45, ht5b, p3152_1, u0elo1]
                    · have p3152_0 := h3152c.1
                      have p3152_1 := h3152c.2.1
                      have p3152_2 := h3152c.2.2.1
                      have p3152_3 := h3152c.2.2.2
                      linarith only [hlam, p3152_0]
                  · linarith only [h2860, h2863, h3096, h3151, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
        · linarith only [h0, h2861, h2866, hlam]
      · linarith only [h0, h2860, h2865, hlam]
    · linarith only [h0, h2859, h2864, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h3241 | h3241
    · rcases m.htr 1 2 4 (by decide) (by decide) with h3242 | h3242
      · rcases m.htr 1 2 5 (by decide) (by decide) with h3243 | h3243
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3244 | h3244
          · linarith only [h2858, h2863, h3244, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3246 | h3246
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3247 | h3247
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3248 | h3248
                · linarith only [h2860, h2863, h3248, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3250 | h3250
                  · linarith only [h2859, h2863, h3246, h3250, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · rcases h2bigk with h3252c | h3252c | h3252c | h3252c | h3252c | h3252c | h3252c | h3252c | h3252c | h3252c | h3252c | h3252c | h3252c | h3252c | h3252c | h3252c | h3252c | h3252c | h3252c | h3252c | h3252c | h3252c | h3252c | h3252c | h3252c
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [hlam, p3252_0]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [h0, hlam, p3252_1]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [h3247, hc35, hlam, hphi, ht0b, ht5b, p3252_1, u0elo1]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      rcases p3252_3 (m.d 0 2) (by simp) with h3256 | h3256
                      · rcases p3252_3 (m.d 1 2) (by simp) with h3257 | h3257
                        · rcases p3252_3 (m.d 2 3) (by simp) with h3258 | h3258
                          · linarith only [h2859, h3258, hlam]
                          · linarith only [h3246, h3258, hlam]
                        · linarith only [h3242, h3257, hlam]
                      · linarith only [h3256, hlam, p3252_0]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      rcases p3252_3 (m.d 0 2) (by simp) with h3263 | h3263
                      · rcases p3252_3 (m.d 1 2) (by simp) with h3264 | h3264
                        · rcases p3252_3 (m.d 2 3) (by simp) with h3265 | h3265
                          · linarith only [h2859, h3265, hlam]
                          · linarith only [h3247, h3265, hlam]
                        · linarith only [h3243, h3264, hlam]
                      · linarith only [h3263, hlam, p3252_0]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [h2859, h3247, h3250, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p3252_1]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [hlam, p3252_0]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      rcases p3252_3 (m.d 0 2) (by simp) with h3272 | h3272
                      · linarith only [h0, h3272, hlam]
                      · linarith only [h2859, h3272, hlam]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      rcases p3252_3 (m.d 0 2) (by simp) with h3275 | h3275
                      · linarith only [h0, h3275, hlam]
                      · linarith only [h2860, h3275, hlam]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      rcases p3252_3 (m.d 0 2) (by simp) with h3278 | h3278
                      · linarith only [h0, h3278, hlam]
                      · linarith only [h2861, h3278, hlam]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [h2859, hlam, p3252_0]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [h3241, hlam, p3252_0]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [hlam, p3252_0]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [h2859, h3246, hc34, hlam, hphi, ht0b, ht45, ht5b, p3252_1, u0elo1]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [h2859, h3247, h3250, hc34, hlam, hphi, ht0b, ht45, ht5b, p3252_1, u0elo1]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [h2860, hlam, p3252_0]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [h3242, hlam, p3252_0]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [h3246, hlam, p3252_1]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [hlam, p3252_0]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [h3248, hlam, p3252_1]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [h2861, hlam, p3252_0]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [h3243, hlam, p3252_0]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [h3247, hlam, p3252_1]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [h2861, h3246, hc34, hlam, hphi, ht0b, ht45, ht5b, p3252_1, u0elo1]
                    · have p3252_0 := h3252c.1
                      have p3252_1 := h3252c.2.1
                      have p3252_2 := h3252c.2.2.1
                      have p3252_3 := h3252c.2.2.2
                      linarith only [hlam, p3252_0]
              · linarith only [h2859, h2862, h3246, h3247, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3297 | h3297
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3298 | h3298
                · linarith only [h2860, h2863, h3298, hlam]
                · linarith only [h3246, h3297, h3298, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3301 | h3301
                · linarith only [h2860, h2863, h3301, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3303 | h3303
                  · linarith only [h2862, h2863, h3303, hlam]
                  · rcases h2bigk with h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c | h3305c
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      linarith only [hlam, p3305_0]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      linarith only [h0, hlam, p3305_1]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      rcases p3305_3 (m.d 0 2) (by simp) with h3308 | h3308
                      · rcases p3305_3 (m.d 1 2) (by simp) with h3309 | h3309
                        · rcases p3305_3 (m.d 2 3) (by simp) with h3310 | h3310
                          · linarith only [h3310, hlam, p3305_0]
                          · rcases p3305_3 (m.d 2 4) (by simp) with h3312 | h3312
                            · linarith only [h2860, h3312, hlam]
                            · linarith only [h3246, h3312, hlam]
                        · linarith only [h3241, h3309, hlam]
                      · linarith only [h3308, hlam, p3305_0]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      rcases p3305_3 (m.d 0 2) (by simp) with h3317 | h3317
                      · rcases p3305_3 (m.d 1 2) (by simp) with h3318 | h3318
                        · rcases p3305_3 (m.d 2 3) (by simp) with h3319 | h3319
                          · linarith only [h2859, h3319, hlam]
                          · rcases p3305_3 (m.d 2 4) (by simp) with h3321 | h3321
                            · linarith only [h3321, hlam, p3305_0]
                            · rcases p3305_3 (m.d 2 5) (by simp) with h3323 | h3323
                              · linarith only [h2861, h3323, hlam]
                              · linarith only [h3301, h3323, hlam]
                        · linarith only [h3242, h3318, hlam]
                      · linarith only [h3317, hlam, p3305_0]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      rcases p3305_3 (m.d 0 2) (by simp) with h3328 | h3328
                      · rcases p3305_3 (m.d 1 2) (by simp) with h3329 | h3329
                        · rcases p3305_3 (m.d 2 3) (by simp) with h3330 | h3330
                          · linarith only [h2859, h3330, hlam]
                          · rcases p3305_3 (m.d 2 4) (by simp) with h3332 | h3332
                            · linarith only [h2860, h3332, hlam]
                            · rcases p3305_3 (m.d 2 5) (by simp) with h3334 | h3334
                              · linarith only [h3334, hlam, p3305_0]
                              · rcases h5bigk with h3336c | h3336c | h3336c | h3336c | h3336c | h3336c | h3336c | h3336c | h3336c | h3336c | h3336c | h3336c | h3336c | h3336c | h3336c | h3336c | h3336c | h3336c | h3336c | h3336c | h3336c | h3336c | h3336c | h3336c | h3336c
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [hlam, p3336_0]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [hc15, hlam, hphi, ht0b, ht5b, p3336_1, u0elo4]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [h0, h2858, h3301, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3336_1]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [h0, h2858, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p3336_1]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [h2863, hlam, p3336_1]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [h2858, hlam, p3336_0]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [hlam, p3336_0]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [h0, h2858, h3301, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p3336_1]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [h0, h2858, h3246, h3303, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3336_1]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [h3244, hlam, p3336_1]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [h2861, hlam, p3336_1]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [h3243, hlam, p3336_1]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [hlam, p3336_0]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [h3297, hlam, p3336_1]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [h3301, hlam, p3336_1]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [h2862, hlam, p3336_0]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [h2859, h2862, hc15, hlam, hphi, ht0b, ht5b, p3336_1, u0elo1]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [h2859, h2862, h3246, h3301, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3336_1, u0elo1]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [hlam, p3336_0]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [h3303, hlam, p3336_1]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [h2858, h3243, h3246, h3301, hc23, hc45, hlam, hphi, ht34, p3336_1]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [h3243, h3246, h3301, hc23, hc45, hlam, hphi, ht34, p3336_1]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [h3246, h3301, hc23, hc45, hlam, hphi, ht34, p3336_1]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [h3297, hc23, hc45, hlam, hphi, ht34, p3336_1]
                                · have p3336_0 := h3336c.1
                                  have p3336_1 := h3336c.2.1
                                  have p3336_2 := h3336c.2.2.1
                                  have p3336_3 := h3336c.2.2.2
                                  linarith only [hlam, p3336_0]
                        · linarith only [h3243, h3329, hlam]
                      · linarith only [h3328, hlam, p3305_0]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      linarith only [h2859, h2862, h3297, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p3305_1]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      linarith only [hlam, p3305_0]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      rcases p3305_3 (m.d 0 2) (by simp) with h3366 | h3366
                      · linarith only [h0, h3366, hlam]
                      · linarith only [h2859, h3366, hlam]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      rcases p3305_3 (m.d 0 2) (by simp) with h3369 | h3369
                      · linarith only [h0, h3369, hlam]
                      · linarith only [h2860, h3369, hlam]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      rcases p3305_3 (m.d 0 2) (by simp) with h3372 | h3372
                      · linarith only [h0, h3372, hlam]
                      · linarith only [h2861, h3372, hlam]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      linarith only [h2859, hlam, p3305_0]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      linarith only [h3241, hlam, p3305_0]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      linarith only [hlam, p3305_0]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      linarith only [h3246, hlam, p3305_0]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      linarith only [h3297, hlam, p3305_0]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      linarith only [h2860, hlam, p3305_0]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      linarith only [h3242, hlam, p3305_0]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      linarith only [h2858, h3243, h3301, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3305_1, u0elo0]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      linarith only [hlam, p3305_0]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      linarith only [h3301, hlam, p3305_1]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      linarith only [h2861, hlam, p3305_0]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      linarith only [h3243, hlam, p3305_0]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      linarith only [h2862, h3297, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3305_1, u0elo2]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      linarith only [h2859, h2862, h3297, hc24, hlam, hphi, ht0b, ht45, ht5b, p3305_1, u0elo1]
                    · have p3305_0 := h3305c.1
                      have p3305_1 := h3305c.2.1
                      have p3305_2 := h3305c.2.2.1
                      have p3305_3 := h3305c.2.2.2
                      linarith only [hlam, p3305_0]
        · linarith only [h0, h2861, h3243, hlam]
      · linarith only [h0, h2860, h3242, hlam]
    · linarith only [h0, h2859, h3241, hlam]

end R2N4
