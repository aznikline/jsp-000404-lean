import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_10S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8068000 in
set_option maxHeartbeats 8068000 in
theorem r1l7_12_24_L_I_H_I_s4_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  exact r1l7_12_24_L_I_H_I_s5 m hb2 hb4 h0 h1 h2 h3 h4 h5

set_option maxHeartbeats 8068000 in
set_option maxHeartbeats 8068000 in
theorem r1l7_12_24_L_I_H_I_s4_x1_x0 (m : N7Model)
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg2 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg3 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h2892 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 1 2 3 (by decide) (by decide) with h2893 | h2893
  · rcases m.htr 1 2 4 (by decide) (by decide) with h2894 | h2894
    · rcases m.htr 1 2 5 (by decide) (by decide) with h2895 | h2895
      · rcases m.htr 1 3 4 (by decide) (by decide) with h2896 | h2896
        · linarith only [h1, h2896, h5, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h2898 | h2898
          · rcases m.htr 2 3 4 (by decide) (by decide) with h2899 | h2899
            · linarith only [h2, h2899, h5, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h2901 | h2901
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2902 | h2902
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2903 | h2903
                  · rcases h2bigk with h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c | h2904c
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [hlam, p2904_0]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [h0, h2893, h2901, h2903, hc01, hc45, hlam, hphi, ht0b, ht5b, p2904_1]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      rcases p2904_3 (m.d 0 2) (by simp) with h2907 | h2907
                      · rcases p2904_3 (m.d 1 2) (by simp) with h2908 | h2908
                        · linarith only [h0, h2908, hlam]
                        · linarith only [h2893, h2908, hlam]
                      · linarith only [h2907, hlam, p2904_0]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      rcases p2904_3 (m.d 0 2) (by simp) with h2912 | h2912
                      · rcases p2904_3 (m.d 1 2) (by simp) with h2913 | h2913
                        · linarith only [h0, h2913, hlam]
                        · linarith only [h2894, h2913, hlam]
                      · linarith only [h2912, hlam, p2904_0]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      rcases p2904_3 (m.d 0 2) (by simp) with h2917 | h2917
                      · rcases p2904_3 (m.d 1 2) (by simp) with h2918 | h2918
                        · linarith only [h0, h2918, hlam]
                        · linarith only [h2895, h2918, hlam]
                      · linarith only [h2917, hlam, p2904_0]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [h0, hlam, p2904_1]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [hlam, p2904_0]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [h0, h2901, h2903, hc01, hc45, hlam, hphi, ht0b, ht5b, p2904_1]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [h0, h2899, h2901, h2903, hc01, hc45, hlam, hphi, ht0b, ht5b, p2904_1]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      rcases p2904_3 (m.d 0 2) (by simp) with h2926 | h2926
                      · rcases p2904_3 (m.d 1 2) (by simp) with h2927 | h2927
                        · rcases p2904_3 (m.d 2 3) (by simp) with h2928 | h2928
                          · linarith only [h2893, h2928, hlam]
                          · linarith only [h2901, h2928, hlam]
                        · linarith only [h2927, hlam, p2904_0]
                      · linarith only [h2926, h4, hlam]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [h2, hlam, p2904_0]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [h2893, hlam, p2904_0]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [hlam, p2904_0]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [h2899, hlam, p2904_1]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [h0, h2893, hc01, hc25, hlam, hphi, ht0b, ht5b, p2904_1]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [h3, hlam, p2904_0]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [h2894, hlam, p2904_0]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [h0, h2901, h3, hc01, hc35, hlam, hphi, ht0b, ht5b, p2904_1]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [hlam, p2904_0]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [h0, h2894, h2901, h2903, hc01, hc45, hlam, hphi, ht0b, ht5b, p2904_1]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [h4, hlam, p2904_0]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [h2895, hlam, p2904_0]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [h2901, hlam, p2904_0]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [h2902, hlam, p2904_1]
                    · have p2904_0 := h2904c.1
                      have p2904_1 := h2904c.2.1
                      have p2904_2 := h2904c.2.2.1
                      have p2904_3 := h2904c.2.2.2
                      linarith only [hlam, p2904_0]
                  · linarith only [h2892, h2903, h5, hlam]
                · linarith only [h0, h2894, h2898, h2899, h2901, h2902, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h2950 | h2950
                · rcases m.htr 3 4 5 (by decide) (by decide) with h2951 | h2951
                  · rcases h2bigk with h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c | h2952c
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [hlam, p2952_0]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [h0, h2894, h2950, hc01, hc45, hlam, hphi, ht0b, ht5b, p2952_1]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      rcases p2952_3 (m.d 0 2) (by simp) with h2955 | h2955
                      · rcases p2952_3 (m.d 1 2) (by simp) with h2956 | h2956
                        · linarith only [h0, h2956, hlam]
                        · linarith only [h2893, h2956, hlam]
                      · linarith only [h2955, hlam, p2952_0]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      rcases p2952_3 (m.d 0 2) (by simp) with h2960 | h2960
                      · rcases p2952_3 (m.d 1 2) (by simp) with h2961 | h2961
                        · linarith only [h0, h2961, hlam]
                        · linarith only [h2894, h2961, hlam]
                      · linarith only [h2960, hlam, p2952_0]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      rcases p2952_3 (m.d 0 2) (by simp) with h2965 | h2965
                      · rcases p2952_3 (m.d 1 2) (by simp) with h2966 | h2966
                        · linarith only [h0, h2966, hlam]
                        · linarith only [h2895, h2966, hlam]
                      · linarith only [h2965, hlam, p2952_0]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [h0, hlam, p2952_1]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [hlam, p2952_0]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      rcases p2952_3 (m.d 0 2) (by simp) with h2972 | h2972
                      · rcases p2952_3 (m.d 1 2) (by simp) with h2973 | h2973
                        · rcases p2952_3 (m.d 2 3) (by simp) with h2974 | h2974
                          · linarith only [h2974, hlam, p2952_0]
                          · rcases p2952_3 (m.d 2 4) (by simp) with h2976 | h2976
                            · linarith only [h2894, h2976, hlam]
                            · linarith only [h2899, h2976, hlam]
                        · linarith only [h2973, hlam, p2952_0]
                      · linarith only [h2, h2972, hlam]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [h0, h2950, hc01, hc45, hlam, hphi, ht0b, ht5b, p2952_1]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      rcases p2952_3 (m.d 0 2) (by simp) with h2982 | h2982
                      · rcases p2952_3 (m.d 1 2) (by simp) with h2983 | h2983
                        · rcases p2952_3 (m.d 2 3) (by simp) with h2984 | h2984
                          · linarith only [h2893, h2984, hlam]
                          · rcases p2952_3 (m.d 2 4) (by simp) with h2986 | h2986
                            · linarith only [h2894, h2986, hlam]
                            · linarith only [h2950, h2986, hlam]
                        · linarith only [h2983, hlam, p2952_0]
                      · linarith only [h2982, h4, hlam]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [h2, hlam, p2952_0]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [h2893, hlam, p2952_0]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [hlam, p2952_0]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [h2899, hlam, p2952_1]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [h2901, hlam, p2952_1]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [h3, hlam, p2952_0]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [h2894, hlam, p2952_0]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [h0, h2894, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2952_1]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [hlam, p2952_0]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [h0, h2894, hc01, hc25, hlam, hphi, ht0b, ht5b, p2952_1]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [h4, hlam, p2952_0]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [h2895, hlam, p2952_0]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [h0, h2895, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p2952_1]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [h2950, hlam, p2952_1]
                    · have p2952_0 := h2952c.1
                      have p2952_1 := h2952c.2.1
                      have p2952_2 := h2952c.2.2.1
                      have p2952_3 := h2952c.2.2.2
                      linarith only [hlam, p2952_0]
                  · linarith only [h2892, h2951, h5, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3007 | h3007
                  · rcases h2bigk with h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c | h3008c
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      linarith only [hlam, p3008_0]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      linarith only [h0, h2894, h2898, h2899, h2950, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3008_1]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      rcases p3008_3 (m.d 0 2) (by simp) with h3011 | h3011
                      · rcases p3008_3 (m.d 1 2) (by simp) with h3012 | h3012
                        · linarith only [h0, h3012, hlam]
                        · linarith only [h2893, h3012, hlam]
                      · linarith only [h3011, hlam, p3008_0]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      rcases p3008_3 (m.d 0 2) (by simp) with h3016 | h3016
                      · rcases p3008_3 (m.d 1 2) (by simp) with h3017 | h3017
                        · linarith only [h0, h3017, hlam]
                        · linarith only [h2894, h3017, hlam]
                      · linarith only [h3016, hlam, p3008_0]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      rcases p3008_3 (m.d 0 2) (by simp) with h3021 | h3021
                      · rcases p3008_3 (m.d 1 2) (by simp) with h3022 | h3022
                        · linarith only [h0, h3022, hlam]
                        · linarith only [h2895, h3022, hlam]
                      · linarith only [h3021, hlam, p3008_0]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      linarith only [h0, hlam, p3008_1]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      linarith only [hlam, p3008_0]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      rcases p3008_3 (m.d 0 2) (by simp) with h3028 | h3028
                      · rcases p3008_3 (m.d 1 2) (by simp) with h3029 | h3029
                        · rcases p3008_3 (m.d 2 3) (by simp) with h3030 | h3030
                          · linarith only [h3030, hlam, p3008_0]
                          · rcases p3008_3 (m.d 2 4) (by simp) with h3032 | h3032
                            · linarith only [h2894, h3032, hlam]
                            · linarith only [h2899, h3032, hlam]
                        · linarith only [h3029, hlam, p3008_0]
                      · linarith only [h2, h3028, hlam]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      rcases p3008_3 (m.d 0 2) (by simp) with h3037 | h3037
                      · rcases p3008_3 (m.d 1 2) (by simp) with h3038 | h3038
                        · rcases p3008_3 (m.d 2 3) (by simp) with h3039 | h3039
                          · linarith only [h2893, h3039, hlam]
                          · rcases p3008_3 (m.d 2 4) (by simp) with h3041 | h3041
                            · linarith only [h3041, hlam, p3008_0]
                            · rcases p3008_3 (m.d 2 5) (by simp) with h3043 | h3043
                              · linarith only [h2895, h3043, hlam]
                              · linarith only [h2950, h3043, hlam]
                        · linarith only [h3038, hlam, p3008_0]
                      · linarith only [h3, h3037, hlam]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      rcases p3008_3 (m.d 0 2) (by simp) with h3048 | h3048
                      · rcases p3008_3 (m.d 1 2) (by simp) with h3049 | h3049
                        · rcases p3008_3 (m.d 2 3) (by simp) with h3050 | h3050
                          · linarith only [h2893, h3050, hlam]
                          · rcases p3008_3 (m.d 2 4) (by simp) with h3052 | h3052
                            · linarith only [h2894, h3052, hlam]
                            · rcases p3008_3 (m.d 2 5) (by simp) with h3054 | h3054
                              · linarith only [h3054, hlam, p3008_0]
                              · rcases h4bigk with h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c | h3056c
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [hlam, p3056_0]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h2898, h2899, h2950, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3056_1]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h2899, h5, hc23, hc34, hlam, hphi, p3056_1]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h5, hlam, p3056_1]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h2899, h2950, h5, hc23, hc34, hlam, hphi, p3056_1]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h1, hlam, p3056_0]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [hlam, p3056_0]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h1, h2899, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3056_1]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h2896, hlam, p3056_1]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h0, h2894, h2899, h2950, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3056_1]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h3, hlam, p3056_0]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h2894, hlam, p3056_0]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [hlam, p3056_0]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h2899, hlam, p3056_1]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h2950, hlam, p3056_0]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h2899, h3, hc23, hc34, hlam, hphi, p3056_1]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h2894, h2899, hc23, hc34, hlam, hphi, p3056_1]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h2899, hc23, hc34, hlam, hphi, p3056_1]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [hlam, p3056_0]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h2899, h2950, hc23, hc34, hlam, hphi, p3056_1]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h2892, hlam, p3056_0]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h2898, hlam, p3056_0]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h1, h2898, h2899, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3056_1]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [h3007, hlam, p3056_0]
                                · have p3056_0 := h3056c.1
                                  have p3056_1 := h3056c.2.1
                                  have p3056_2 := h3056c.2.2.1
                                  have p3056_3 := h3056c.2.2.2
                                  linarith only [hlam, p3056_0]
                        · linarith only [h3049, hlam, p3008_0]
                      · linarith only [h3048, h4, hlam]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      linarith only [h2, hlam, p3008_0]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      linarith only [h2893, hlam, p3008_0]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      linarith only [hlam, p3008_0]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      linarith only [h2899, hlam, p3008_1]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      linarith only [h2901, hlam, p3008_1]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      linarith only [h3, hlam, p3008_0]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      linarith only [h2894, hlam, p3008_0]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      linarith only [h0, h2894, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3008_1]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      linarith only [hlam, p3008_0]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      linarith only [h2950, hlam, p3008_0]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      linarith only [h4, hlam, p3008_0]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      linarith only [h2895, hlam, p3008_0]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      linarith only [h0, h2895, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3008_1]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      linarith only [h0, h2894, h2898, h2950, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3008_1]
                    · have p3008_0 := h3008c.1
                      have p3008_1 := h3008c.2.1
                      have p3008_2 := h3008c.2.2.1
                      have p3008_3 := h3008c.2.2.2
                      linarith only [hlam, p3008_0]
                  · linarith only [h0, h2894, h2898, h3007, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3100 | h3100
            · linarith only [h2892, h2893, h2896, h2898, h3100, h5, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3102 | h3102
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3103 | h3103
                · linarith only [h0, h2893, h2896, h2898, h3, h3102, h3103, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h3100, h3102, h3103, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3106 | h3106
                · linarith only [h0, h2894, h2896, h2898, h3106, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3108 | h3108
                  · rcases h2bigk with h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c | h3109c
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      linarith only [hlam, p3109_0]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      rcases p3109_3 (m.d 0 2) (by simp) with h3111 | h3111
                      · rcases p3109_3 (m.d 1 2) (by simp) with h3112 | h3112
                        · linarith only [h0, h3112, hlam]
                        · rcases p3109_3 (m.d 2 3) (by simp) with h3114 | h3114
                          · linarith only [h2, h3114, hlam]
                          · rcases p3109_3 (m.d 2 4) (by simp) with h3116 | h3116
                            · linarith only [h3, h3116, hlam]
                            · rcases p3109_3 (m.d 2 5) (by simp) with h3118 | h3118
                              · linarith only [h3118, h4, hlam]
                              · rcases h4bigk with h3120c | h3120c | h3120c | h3120c | h3120c | h3120c | h3120c | h3120c | h3120c | h3120c | h3120c | h3120c | h3120c | h3120c | h3120c | h3120c | h3120c | h3120c | h3120c | h3120c | h3120c | h3120c | h3120c | h3120c | h3120c
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [hlam, p3120_0]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h2893, h2896, h5, hc23, hc34, hlam, hphi, p3120_1]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h3100, h5, hc23, hc34, hlam, hphi, p3120_1]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h5, hlam, p3120_1]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h2893, h2896, h2898, h5, hc23, hc34, hlam, hphi, p3120_1]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h1, hlam, p3120_0]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [hlam, p3120_0]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h2898, h3100, h3108, hc23, hc35, hlam, hphi, p3120_1]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h2896, hlam, p3120_1]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h2898, hlam, p3120_0]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h3, hlam, p3120_0]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h2894, hlam, p3120_0]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [hlam, p3120_0]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h3100, hlam, p3120_1]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h3106, hlam, p3120_0]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h3, h3100, hc23, hc34, hlam, hphi, p3120_1]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h2894, h3100, hc23, hc34, hlam, hphi, p3120_1]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h3100, hc23, hc34, hlam, hphi, p3120_1]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [hlam, p3120_0]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h2894, h2898, h3100, hc23, hc34, hlam, hphi, p3120_1]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h2892, hlam, p3120_0]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h2892, h2894, h3100, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3120_1]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h2892, h3100, h5, hc23, hc34, hlam, hphi, p3120_1]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [h3108, hlam, p3120_0]
                                · have p3120_0 := h3120c.1
                                  have p3120_1 := h3120c.2.1
                                  have p3120_2 := h3120c.2.2.1
                                  have p3120_3 := h3120c.2.2.2
                                  linarith only [hlam, p3120_0]
                      · linarith only [h0, h3111, hlam]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      rcases p3109_3 (m.d 0 2) (by simp) with h3147 | h3147
                      · rcases p3109_3 (m.d 1 2) (by simp) with h3148 | h3148
                        · linarith only [h0, h3148, hlam]
                        · linarith only [h2893, h3148, hlam]
                      · linarith only [h3147, hlam, p3109_0]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      rcases p3109_3 (m.d 0 2) (by simp) with h3152 | h3152
                      · rcases p3109_3 (m.d 1 2) (by simp) with h3153 | h3153
                        · linarith only [h0, h3153, hlam]
                        · linarith only [h2894, h3153, hlam]
                      · linarith only [h3152, hlam, p3109_0]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      rcases p3109_3 (m.d 0 2) (by simp) with h3157 | h3157
                      · rcases p3109_3 (m.d 1 2) (by simp) with h3158 | h3158
                        · linarith only [h0, h3158, hlam]
                        · linarith only [h2895, h3158, hlam]
                      · linarith only [h3157, hlam, p3109_0]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      linarith only [h0, hlam, p3109_1]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      linarith only [hlam, p3109_0]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      rcases p3109_3 (m.d 0 2) (by simp) with h3164 | h3164
                      · rcases p3109_3 (m.d 1 2) (by simp) with h3165 | h3165
                        · rcases p3109_3 (m.d 2 3) (by simp) with h3166 | h3166
                          · linarith only [h3166, hlam, p3109_0]
                          · rcases p3109_3 (m.d 2 4) (by simp) with h3168 | h3168
                            · linarith only [h2894, h3168, hlam]
                            · linarith only [h3100, h3168, hlam]
                        · linarith only [h3165, hlam, p3109_0]
                      · linarith only [h2, h3164, hlam]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      rcases p3109_3 (m.d 0 2) (by simp) with h3173 | h3173
                      · rcases p3109_3 (m.d 1 2) (by simp) with h3174 | h3174
                        · rcases p3109_3 (m.d 2 3) (by simp) with h3175 | h3175
                          · linarith only [h2893, h3175, hlam]
                          · rcases p3109_3 (m.d 2 4) (by simp) with h3177 | h3177
                            · linarith only [h3177, hlam, p3109_0]
                            · rcases p3109_3 (m.d 2 5) (by simp) with h3179 | h3179
                              · linarith only [h2895, h3179, hlam]
                              · linarith only [h3106, h3179, hlam]
                        · linarith only [h3174, hlam, p3109_0]
                      · linarith only [h3, h3173, hlam]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      rcases p3109_3 (m.d 0 2) (by simp) with h3184 | h3184
                      · rcases p3109_3 (m.d 1 2) (by simp) with h3185 | h3185
                        · rcases p3109_3 (m.d 2 3) (by simp) with h3186 | h3186
                          · linarith only [h2893, h3186, hlam]
                          · rcases p3109_3 (m.d 2 4) (by simp) with h3188 | h3188
                            · linarith only [h2894, h3188, hlam]
                            · rcases p3109_3 (m.d 2 5) (by simp) with h3190 | h3190
                              · linarith only [h3190, hlam, p3109_0]
                              · rcases h4bigk with h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c | h3192c
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [hlam, p3192_0]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h2894, h3100, h5, hc23, hc34, hlam, hphi, p3192_1]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h3100, h5, hc23, hc34, hlam, hphi, p3192_1]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h5, hlam, p3192_1]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h2895, h2898, h3100, h3106, h5, hc23, hc34, hlam, hphi, p3192_1]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h1, hlam, p3192_0]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [hlam, p3192_0]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h1, h3100, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3192_1]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h2896, hlam, p3192_1]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h2898, hlam, p3192_0]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h3, hlam, p3192_0]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h2894, hlam, p3192_0]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [hlam, p3192_0]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h3100, hlam, p3192_1]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h3106, hlam, p3192_0]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h3, h3100, hc23, hc34, hlam, hphi, p3192_1]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h2894, h3100, hc23, hc34, hlam, hphi, p3192_1]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h3100, hc23, hc34, hlam, hphi, p3192_1]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [hlam, p3192_0]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h2894, h2898, h3100, hc23, hc34, hlam, hphi, p3192_1]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h2892, hlam, p3192_0]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h2892, h2894, h3100, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3192_1]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h2892, h3100, h5, hc23, hc34, hlam, hphi, p3192_1]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [h3108, hlam, p3192_0]
                                · have p3192_0 := h3192c.1
                                  have p3192_1 := h3192c.2.1
                                  have p3192_2 := h3192c.2.2.1
                                  have p3192_3 := h3192c.2.2.2
                                  linarith only [hlam, p3192_0]
                        · linarith only [h3185, hlam, p3109_0]
                      · linarith only [h3184, h4, hlam]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      linarith only [h2, hlam, p3109_0]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      linarith only [h2893, hlam, p3109_0]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      linarith only [hlam, p3109_0]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      linarith only [h3100, hlam, p3109_1]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      linarith only [h3102, hlam, p3109_1]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      linarith only [h3, hlam, p3109_0]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      linarith only [h2894, hlam, p3109_0]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      linarith only [h0, h2894, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3109_1]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      linarith only [hlam, p3109_0]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      linarith only [h3106, hlam, p3109_0]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      linarith only [h4, hlam, p3109_0]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      linarith only [h2895, hlam, p3109_0]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      linarith only [h0, h2895, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3109_1]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      linarith only [h0, h2895, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p3109_1]
                    · have p3109_0 := h3109c.1
                      have p3109_1 := h3109c.2.1
                      have p3109_2 := h3109c.2.2.1
                      have p3109_3 := h3109c.2.2.2
                      linarith only [hlam, p3109_0]
                  · linarith only [h2892, h3108, h5, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3236 | h3236
        · linarith only [h2892, h2893, h2895, h3236, h4, h5, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3238 | h3238
          · linarith only [h2894, h2895, h3238, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3240 | h3240
            · linarith only [h2892, h2893, h2895, h3236, h3238, h3240, h4, h5, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3242 | h3242
              · linarith only [h0, h2893, h2895, h3242, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3244 | h3244
                · linarith only [h0, h2893, h2894, h2895, h3236, h3238, h3244, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h2892, h2893, h2895, h3244, h5, hc23, hc34, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h3247 | h3247
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3248 | h3248
        · linarith only [h1, h2893, h2894, h3248, h5, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3250 | h3250
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3251 | h3251
            · linarith only [h0, h2, h2894, h3, h3247, h3251, h5, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3253 | h3253
              · linarith only [h0, h2893, h2894, h3, h3253, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3255 | h3255
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3256 | h3256
                  · rcases h2bigk with h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c | h3257c
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [hlam, p3257_0]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      rcases p3257_3 (m.d 0 2) (by simp) with h3259 | h3259
                      · rcases p3257_3 (m.d 1 2) (by simp) with h3260 | h3260
                        · linarith only [h0, h3260, hlam]
                        · rcases p3257_3 (m.d 2 3) (by simp) with h3262 | h3262
                          · linarith only [h2, h3262, hlam]
                          · rcases p3257_3 (m.d 2 4) (by simp) with h3264 | h3264
                            · linarith only [h3, h3264, hlam]
                            · linarith only [h2894, h3264, hlam]
                      · linarith only [h0, h3259, hlam]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [h2894, h3, h3247, h3253, hlam, p3257_2]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [h0, h2894, h3247, h3253, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3257_1]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [h2894, h3, h3247, hlam, p3257_2]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [h0, hlam, p3257_1]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [hlam, p3257_0]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [h2894, h3, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3257_1]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [h2894, hlam, p3257_0]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [h2894, h3, hc02, hc25, hlam, hphi, ht0b, ht5b, p3257_1]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [h2, hlam, p3257_0]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [h2893, hlam, p3257_0]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [hlam, p3257_0]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [h3251, hlam, p3257_1]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [h3253, hlam, p3257_1]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [h3, hlam, p3257_0]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [h0, h2893, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3257_1]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      rcases p3257_3 (m.d 0 2) (by simp) with h3283 | h3283
                      · rcases p3257_3 (m.d 1 2) (by simp) with h3284 | h3284
                        · linarith only [h2894, h3284, hlam]
                        · linarith only [h2893, h3284, hlam]
                      · linarith only [h2, h3283, hlam]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [hlam, p3257_0]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      rcases p3257_3 (m.d 0 2) (by simp) with h3289 | h3289
                      · rcases p3257_3 (m.d 1 2) (by simp) with h3290 | h3290
                        · linarith only [h2894, h3290, hlam]
                        · linarith only [h3247, h3290, hlam]
                      · linarith only [h3289, h4, hlam]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [h4, hlam, p3257_0]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [h3247, hlam, p3257_0]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [h0, h3247, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3257_1]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [h3255, hlam, p3257_1]
                    · have p3257_0 := h3257c.1
                      have p3257_1 := h3257c.2.1
                      have p3257_2 := h3257c.2.2.1
                      have p3257_3 := h3257c.2.2.2
                      linarith only [hlam, p3257_0]
                  · linarith only [h2892, h3256, h5, hlam]
                · linarith only [h2894, h3247, h3253, h3255, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h2892, h2893, h2894, h3250, h5, hc23, hc34, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3302 | h3302
        · linarith only [h0, h2893, h2894, h3, h3302, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3304 | h3304
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3305 | h3305
            · linarith only [h2892, h2893, h3247, h3305, h4, h5, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3307 | h3307
              · linarith only [h0, h2893, h3247, h3307, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3309 | h3309
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3310 | h3310
                  · rcases h2bigk with h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c | h3311c
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [hlam, p3311_0]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      rcases p3311_3 (m.d 0 2) (by simp) with h3313 | h3313
                      · rcases p3311_3 (m.d 1 2) (by simp) with h3314 | h3314
                        · linarith only [h0, h3314, hlam]
                        · rcases p3311_3 (m.d 2 3) (by simp) with h3316 | h3316
                          · linarith only [h2, h3316, hlam]
                          · rcases p3311_3 (m.d 2 4) (by simp) with h3318 | h3318
                            · linarith only [h3, h3318, hlam]
                            · linarith only [h2894, h3318, hlam]
                      · linarith only [h0, h3313, hlam]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [h2893, h3, h3247, h3309, hlam, p3311_2]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [h0, h2893, h3247, h3309, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3311_1]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [h0, h2893, h3247, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3311_1]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [h0, hlam, p3311_1]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [hlam, p3311_0]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [h3247, h3307, hc23, hc35, hlam, hphi, p3311_1]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [h2894, hlam, p3311_0]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [h3247, hlam, p3311_0]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [h2, hlam, p3311_0]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [h2893, hlam, p3311_0]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [hlam, p3311_0]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [h3305, hlam, p3311_1]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [h3307, hlam, p3311_1]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [h3, hlam, p3311_0]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [h2893, h3, h5, hc23, hc34, hlam, hphi, p3311_1]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      rcases p3311_3 (m.d 0 2) (by simp) with h3337 | h3337
                      · rcases p3311_3 (m.d 1 2) (by simp) with h3338 | h3338
                        · linarith only [h2894, h3338, hlam]
                        · linarith only [h2893, h3338, hlam]
                      · linarith only [h2, h3337, hlam]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [hlam, p3311_0]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [h0, h2893, h3, h3247, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3311_1]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [h4, hlam, p3311_0]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [h0, h2893, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p3311_1]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      rcases p3311_3 (m.d 0 2) (by simp) with h3346 | h3346
                      · rcases p3311_3 (m.d 1 2) (by simp) with h3347 | h3347
                        · linarith only [h3247, h3347, hlam]
                        · linarith only [h2893, h3347, hlam]
                      · linarith only [h2, h3346, hlam]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [h3309, hlam, p3311_1]
                    · have p3311_0 := h3311c.1
                      have p3311_1 := h3311c.2.1
                      have p3311_2 := h3311c.2.2.1
                      have p3311_3 := h3311c.2.2.2
                      linarith only [hlam, p3311_0]
                  · linarith only [h1, h3304, h3310, h5, hlam]
                · linarith only [h2893, h2894, h3309, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h2892, h2893, h2894, h3304, h5, hc23, hc34, hlam, hphi]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h3356 | h3356
    · rcases m.htr 1 2 5 (by decide) (by decide) with h3357 | h3357
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3358 | h3358
        · linarith only [h2, h2893, h3357, h3358, h5, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
        · linarith only [h2893, h3356, h3358, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3361 | h3361
        · linarith only [h2, h2893, h3361, h5, hlam]
        · linarith only [h2893, h3356, h3361, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h3364 | h3364
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3365 | h3365
        · linarith only [h2, h2893, h3364, h3365, h5, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3367 | h3367
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3368 | h3368
            · linarith only [h2, h3368, h5, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3370 | h3370
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3371 | h3371
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3372 | h3372
                  · rcases h2bigk with h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c | h3373c
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [hlam, p3373_0]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      rcases p3373_3 (m.d 0 2) (by simp) with h3375 | h3375
                      · rcases p3373_3 (m.d 1 2) (by simp) with h3376 | h3376
                        · linarith only [h0, h3376, hlam]
                        · rcases p3373_3 (m.d 2 3) (by simp) with h3378 | h3378
                          · linarith only [h2, h3378, hlam]
                          · linarith only [h2893, h3378, hlam]
                      · linarith only [h0, h3375, hlam]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [h0, h2893, h3364, h3370, h3372, hc01, hc45, hlam, hphi, ht0b, ht5b, p3373_1]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [h0, h2893, h3364, h3368, h3370, h3372, hc01, hc45, hlam, hphi, ht0b, ht5b, p3373_1]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [h2, h2893, h3364, hlam, p3373_2]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [h0, hlam, p3373_1]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [hlam, p3373_0]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [h2893, hlam, p3373_0]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [h3356, hlam, p3373_0]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [h2, h2893, h3370, h3372, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3373_1]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [h2, hlam, p3373_0]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [h2, h5, hc12, hc34, hlam, hphi, ht23, p3373_1]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [hlam, p3373_0]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [h3368, hlam, p3373_1]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      rcases p3373_3 (m.d 0 2) (by simp) with h3394 | h3394
                      · rcases p3373_3 (m.d 1 2) (by simp) with h3395 | h3395
                        · linarith only [h2893, h3395, hlam]
                        · linarith only [h3364, h3395, hlam]
                      · linarith only [h3394, h4, hlam]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [h3, hlam, p3373_0]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [h3, h3364, h3370, h3372, hc02, hc45, hlam, hphi, ht0b, ht5b, p3373_1]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [h0, h2893, h3, h3364, h3370, h3372, hc01, hc45, hlam, hphi, ht0b, ht5b, p3373_1]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [hlam, p3373_0]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      rcases p3373_3 (m.d 0 2) (by simp) with h3403 | h3403
                      · rcases p3373_3 (m.d 1 2) (by simp) with h3404 | h3404
                        · linarith only [h3356, h3404, hlam]
                        · linarith only [h3364, h3404, hlam]
                      · linarith only [h3403, h4, hlam]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [h4, hlam, p3373_0]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [h3364, hlam, p3373_0]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [h3370, hlam, p3373_0]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [h3371, hlam, p3373_1]
                    · have p3373_0 := h3373c.1
                      have p3373_1 := h3373c.2.1
                      have p3373_2 := h3373c.2.2.1
                      have p3373_3 := h3373c.2.2.2
                      linarith only [hlam, p3373_0]
                  · linarith only [h2, h2893, h3372, h5, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h3356, h3364, h3367, h3370, h3371, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
              · linarith only [h2893, h3364, h3370, hlam]
          · linarith only [h2893, h3364, h3365, h3367, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h3417 | h3417
        · linarith only [h2, h2893, h3417, h5, hlam]
        · rcases m.htr 1 4 5 (by decide) (by decide) with h3419 | h3419
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3420 | h3420
            · linarith only [h2, h3420, h5, hlam]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3422 | h3422
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3423 | h3423
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3424 | h3424
                  · rcases h2bigk with h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c | h3425c
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [hlam, p3425_0]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      rcases p3425_3 (m.d 0 2) (by simp) with h3427 | h3427
                      · rcases p3425_3 (m.d 1 2) (by simp) with h3428 | h3428
                        · linarith only [h0, h3428, hlam]
                        · rcases p3425_3 (m.d 2 3) (by simp) with h3430 | h3430
                          · linarith only [h2, h3430, hlam]
                          · linarith only [h2893, h3430, hlam]
                      · linarith only [h0, h3427, hlam]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      rcases p3425_3 (m.d 0 2) (by simp) with h3434 | h3434
                      · rcases p3425_3 (m.d 1 2) (by simp) with h3435 | h3435
                        · linarith only [h0, h3435, hlam]
                        · rcases p3425_3 (m.d 2 3) (by simp) with h3437 | h3437
                          · linarith only [h3437, hlam, p3425_0]
                          · rcases p3425_3 (m.d 2 4) (by simp) with h3439 | h3439
                            · linarith only [h3, h3439, hlam]
                            · linarith only [h3420, h3439, hlam]
                      · linarith only [h3434, hlam, p3425_0]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      rcases p3425_3 (m.d 0 2) (by simp) with h3443 | h3443
                      · rcases p3425_3 (m.d 1 2) (by simp) with h3444 | h3444
                        · linarith only [h0, h3444, hlam]
                        · rcases p3425_3 (m.d 2 3) (by simp) with h3446 | h3446
                          · linarith only [h2, h3446, hlam]
                          · rcases p3425_3 (m.d 2 4) (by simp) with h3448 | h3448
                            · linarith only [h3448, hlam, p3425_0]
                            · rcases p3425_3 (m.d 2 5) (by simp) with h3450 | h3450
                              · linarith only [h3450, h4, hlam]
                              · rcases h4bigk with h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c | h3452c
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [hlam, p3452_0]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [h0, h3364, h3419, h3420, h3422, h5, hc01, hc12, hc34, hc45, hlam, hphi, ht0b, ht23, ht5b, p3425_1, p3452_1]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [h3364, h3420, h3422, h5, hc12, hc34, hlam, hphi, ht23, p3452_1]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [h5, hlam, p3452_1]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  rcases p3452_3 (m.d 0 4) (by simp) with h3457 | h3457
                                  · rcases p3452_3 (m.d 1 4) (by simp) with h3458 | h3458
                                    · linarith only [h1, h3458, hlam]
                                    · linarith only [h3419, h3458, hlam]
                                  · linarith only [h3457, hlam, p3452_0]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [h1, hlam, p3452_0]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [hlam, p3452_0]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [h3356, hlam, p3452_1]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [h3417, hlam, p3452_1]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [h1, hc01, hc45, hlam, hphi, ht0b, ht5b, p3452_1]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [h3, hlam, p3452_0]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3425_1, p3452_1]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [hlam, p3452_0]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [h3420, hlam, p3452_1]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p3425_1, p3452_1]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [h0, h1, h3364, h3419, h3420, h3422, hc01, hc12, hc34, hc45, hlam, hphi, ht0b, ht23, ht5b, p3425_1, p3452_1]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [h0, h3364, h3419, h3420, h3422, hc01, hc12, hc34, hc45, hlam, hphi, ht0b, ht23, ht5b, p3425_1, p3452_1]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [h3364, h3420, h3422, hc12, hc34, hlam, hphi, ht23, p3452_1]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [hlam, p3452_0]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  rcases p3452_3 (m.d 0 4) (by simp) with h3476 | h3476
                                  · linarith only [h3476, h5, hlam]
                                  · linarith only [h2892, h3476, hlam]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [h2892, hlam, p3452_0]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [h3419, hlam, p3452_0]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [h3423, hlam, p3452_0]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [h3424, hlam, p3452_0]
                                · have p3452_0 := h3452c.1
                                  have p3452_1 := h3452c.2.1
                                  have p3452_2 := h3452c.2.2.1
                                  have p3452_3 := h3452c.2.2.2
                                  linarith only [hlam, p3452_0]
                      · linarith only [h3443, hlam, p3425_0]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      rcases p3425_3 (m.d 0 2) (by simp) with h3485 | h3485
                      · rcases p3425_3 (m.d 1 2) (by simp) with h3486 | h3486
                        · linarith only [h0, h3486, hlam]
                        · rcases p3425_3 (m.d 2 3) (by simp) with h3488 | h3488
                          · linarith only [h2, h3488, hlam]
                          · linarith only [h3422, h3488, hlam]
                      · linarith only [h3485, hlam, p3425_0]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [h0, hlam, p3425_1]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [hlam, p3425_0]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [h2893, hlam, p3425_0]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [h3356, hlam, p3425_0]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [h3364, hlam, p3425_0]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [h2, hlam, p3425_0]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [h2, h5, hc12, hc34, hlam, hphi, ht23, p3425_1]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [hlam, p3425_0]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [h3420, hlam, p3425_1]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [h2, h3364, h5, hc12, hc34, hlam, hphi, ht23, p3425_1]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [h3, hlam, p3425_0]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      rcases p3425_3 (m.d 0 2) (by simp) with h3503 | h3503
                      · rcases p3425_3 (m.d 1 2) (by simp) with h3504 | h3504
                        · linarith only [h3504, hlam, p3425_0]
                        · rcases p3425_3 (m.d 2 3) (by simp) with h3506 | h3506
                          · linarith only [h3420, h3506, hlam]
                          · linarith only [h2893, h3506, hlam]
                      · linarith only [h0, h3503, hlam]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [h0, h3, h3422, hc01, hc35, hlam, hphi, ht0b, ht5b, p3425_1]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [hlam, p3425_0]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [h0, h3, h3364, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3425_1]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [h4, hlam, p3425_0]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [h2, h3422, h5, hc12, hc34, hlam, hphi, ht23, p3425_1]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [h3422, hlam, p3425_0]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [h3423, hlam, p3425_1]
                    · have p3425_0 := h3425c.1
                      have p3425_1 := h3425c.2.1
                      have p3425_2 := h3425c.2.2.1
                      have p3425_3 := h3425c.2.2.2
                      linarith only [hlam, p3425_0]
                  · linarith only [h1, h3419, h3424, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h2, h3356, h3364, h3419, h3422, h3423, h5, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3520 | h3520
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3521 | h3521
                  · rcases h2bigk with h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c | h3522c
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      linarith only [hlam, p3522_0]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      rcases p3522_3 (m.d 0 2) (by simp) with h3524 | h3524
                      · rcases p3522_3 (m.d 1 2) (by simp) with h3525 | h3525
                        · linarith only [h0, h3525, hlam]
                        · rcases p3522_3 (m.d 2 3) (by simp) with h3527 | h3527
                          · linarith only [h2, h3527, hlam]
                          · linarith only [h2893, h3527, hlam]
                      · linarith only [h0, h3524, hlam]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      rcases p3522_3 (m.d 0 2) (by simp) with h3531 | h3531
                      · rcases p3522_3 (m.d 1 2) (by simp) with h3532 | h3532
                        · linarith only [h0, h3532, hlam]
                        · rcases p3522_3 (m.d 2 3) (by simp) with h3534 | h3534
                          · linarith only [h3534, hlam, p3522_0]
                          · rcases p3522_3 (m.d 2 4) (by simp) with h3536 | h3536
                            · linarith only [h3, h3536, hlam]
                            · linarith only [h3420, h3536, hlam]
                      · linarith only [h3531, hlam, p3522_0]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      rcases p3522_3 (m.d 0 2) (by simp) with h3540 | h3540
                      · rcases p3522_3 (m.d 1 2) (by simp) with h3541 | h3541
                        · linarith only [h0, h3541, hlam]
                        · rcases p3522_3 (m.d 2 3) (by simp) with h3543 | h3543
                          · linarith only [h2, h3543, hlam]
                          · rcases p3522_3 (m.d 2 4) (by simp) with h3545 | h3545
                            · linarith only [h3545, hlam, p3522_0]
                            · rcases p3522_3 (m.d 2 5) (by simp) with h3547 | h3547
                              · linarith only [h3547, h4, hlam]
                              · rcases h4bigk with h3549c | h3549c | h3549c | h3549c | h3549c | h3549c | h3549c | h3549c | h3549c | h3549c | h3549c | h3549c | h3549c | h3549c | h3549c | h3549c | h3549c | h3549c | h3549c | h3549c | h3549c | h3549c | h3549c | h3549c | h3549c
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [hlam, p3549_0]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [h3419, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p3549_1]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [h2893, h3422, h3520, h5, hc12, hc34, hlam, hphi, ht23, p3549_1]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [h5, hlam, p3549_1]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  rcases p3549_3 (m.d 0 4) (by simp) with h3554 | h3554
                                  · rcases p3549_3 (m.d 1 4) (by simp) with h3555 | h3555
                                    · linarith only [h1, h3555, hlam]
                                    · linarith only [h3419, h3555, hlam]
                                  · linarith only [h3554, hlam, p3549_0]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [h1, hlam, p3549_0]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [hlam, p3549_0]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [h3356, hlam, p3549_1]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [h3417, hlam, p3549_1]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [h1, hc01, hc45, hlam, hphi, ht0b, ht5b, p3549_1]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [h3, hlam, p3549_0]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [h0, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p3522_1, p3549_1]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [hlam, p3549_0]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [h3420, hlam, p3549_1]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p3522_1, p3549_1]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [h0, h1, h2893, h3419, h3422, h3520, hc01, hc12, hc34, hc45, hlam, hphi, ht0b, ht23, ht5b, p3522_1, p3549_1]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [h0, h2893, h3419, h3422, h3520, hc01, hc12, hc34, hc45, hlam, hphi, ht0b, ht23, ht5b, p3522_1, p3549_1]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [h2893, h3422, h3520, hc12, hc34, hlam, hphi, ht23, p3549_1]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [hlam, p3549_0]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  rcases p3549_3 (m.d 0 4) (by simp) with h3573 | h3573
                                  · linarith only [h3573, h5, hlam]
                                  · linarith only [h2892, h3573, hlam]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [h2892, hlam, p3549_0]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [h3419, hlam, p3549_0]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [h3520, hlam, p3549_0]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [h3521, hlam, p3549_0]
                                · have p3549_0 := h3549c.1
                                  have p3549_1 := h3549c.2.1
                                  have p3549_2 := h3549c.2.2.1
                                  have p3549_3 := h3549c.2.2.2
                                  linarith only [hlam, p3549_0]
                      · linarith only [h3540, hlam, p3522_0]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      rcases p3522_3 (m.d 0 2) (by simp) with h3582 | h3582
                      · rcases p3522_3 (m.d 1 2) (by simp) with h3583 | h3583
                        · linarith only [h0, h3583, hlam]
                        · rcases p3522_3 (m.d 2 3) (by simp) with h3585 | h3585
                          · linarith only [h2, h3585, hlam]
                          · rcases p3522_3 (m.d 2 4) (by simp) with h3587 | h3587
                            · linarith only [h3, h3587, hlam]
                            · linarith only [h3520, h3587, hlam]
                      · linarith only [h3582, hlam, p3522_0]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      linarith only [h0, hlam, p3522_1]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      linarith only [hlam, p3522_0]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      linarith only [h2893, hlam, p3522_0]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      linarith only [h3356, hlam, p3522_0]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      linarith only [h3364, hlam, p3522_0]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      linarith only [h2, hlam, p3522_0]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      linarith only [h3422, hc12, hc35, hlam, hphi, ht23, p3522_1]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      linarith only [hlam, p3522_0]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      linarith only [h3420, hlam, p3522_1]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      linarith only [h3422, hlam, p3522_1]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      linarith only [h3, hlam, p3522_0]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      rcases p3522_3 (m.d 0 2) (by simp) with h3602 | h3602
                      · rcases p3522_3 (m.d 1 2) (by simp) with h3603 | h3603
                        · linarith only [h3603, hlam, p3522_0]
                        · rcases p3522_3 (m.d 2 3) (by simp) with h3605 | h3605
                          · linarith only [h3420, h3605, hlam]
                          · linarith only [h2893, h3605, hlam]
                      · linarith only [h0, h3602, hlam]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      linarith only [h0, h2893, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3522_1]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      linarith only [hlam, p3522_0]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      linarith only [h0, h2893, h3, h3422, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3522_1]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      linarith only [h4, hlam, p3522_0]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      rcases p3522_3 (m.d 0 2) (by simp) with h3613 | h3613
                      · rcases p3522_3 (m.d 1 2) (by simp) with h3614 | h3614
                        · linarith only [h3614, hlam, p3522_0]
                        · rcases p3522_3 (m.d 2 3) (by simp) with h3616 | h3616
                          · linarith only [h3422, h3616, hlam]
                          · linarith only [h2893, h3616, hlam]
                      · linarith only [h0, h3613, hlam]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      linarith only [h2893, hc12, hc25, hlam, hphi, p3522_1]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      linarith only [h3520, hlam, p3522_1]
                    · have p3522_0 := h3522c.1
                      have p3522_1 := h3522c.2.1
                      have p3522_2 := h3522c.2.2.1
                      have p3522_3 := h3522c.2.2.2
                      linarith only [hlam, p3522_0]
                  · linarith only [h1, h3419, h3521, h5, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h3356, h3419, h3520, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h3625 | h3625
            · linarith only [h2892, h2893, h3417, h3419, h3625, h5, hc12, hc23, hlam, hphi]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h3627 | h3627
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3628 | h3628
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3629 | h3629
                  · linarith only [h2, h2893, h3417, h3419, h3627, h3629, h5, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h2, h3627, h3628, h3629, h5, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h2892, h3356, h3628, h5, hc12, hc34, hlam, hphi, ht23]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h3633 | h3633
                · rcases m.htr 3 4 5 (by decide) (by decide) with h3634 | h3634
                  · rcases h2bigk with h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c | h3635c
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h2893, h3, h3417, h3419, h3633, hlam, p3635_2]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      rcases p3635_3 (m.d 0 2) (by simp) with h3638 | h3638
                      · rcases p3635_3 (m.d 1 2) (by simp) with h3639 | h3639
                        · linarith only [h0, h3639, hlam]
                        · rcases p3635_3 (m.d 2 3) (by simp) with h3641 | h3641
                          · linarith only [h3641, hlam, p3635_0]
                          · rcases p3635_3 (m.d 2 4) (by simp) with h3643 | h3643
                            · linarith only [h3, h3643, hlam]
                            · linarith only [h3625, h3643, hlam]
                      · linarith only [h3638, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h0, h2893, h3417, h3419, h3633, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3635_1]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      rcases p3635_3 (m.d 0 2) (by simp) with h3648 | h3648
                      · rcases p3635_3 (m.d 1 2) (by simp) with h3649 | h3649
                        · linarith only [h0, h3649, hlam]
                        · rcases p3635_3 (m.d 2 3) (by simp) with h3651 | h3651
                          · linarith only [h2, h3651, hlam]
                          · rcases p3635_3 (m.d 2 4) (by simp) with h3653 | h3653
                            · linarith only [h3, h3653, hlam]
                            · linarith only [h3633, h3653, hlam]
                      · linarith only [h3648, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h0, hlam, p3635_1]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h2893, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h3356, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h3364, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h2, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h3627, hc12, hc35, hlam, hphi, ht23, p3635_1]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h3625, hlam, p3635_1]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h3627, hlam, p3635_1]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h3, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      rcases p3635_3 (m.d 0 2) (by simp) with h3668 | h3668
                      · rcases p3635_3 (m.d 1 2) (by simp) with h3669 | h3669
                        · linarith only [h3669, hlam, p3635_0]
                        · rcases p3635_3 (m.d 2 3) (by simp) with h3671 | h3671
                          · linarith only [h3625, h3671, hlam]
                          · linarith only [h2893, h3671, hlam]
                      · linarith only [h0, h3668, hlam]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h0, h2893, h3, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3635_1]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h0, h2893, h3, h3627, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p3635_1]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h4, hlam, p3635_0]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      rcases p3635_3 (m.d 0 2) (by simp) with h3679 | h3679
                      · rcases p3635_3 (m.d 1 2) (by simp) with h3680 | h3680
                        · linarith only [h3680, hlam, p3635_0]
                        · rcases p3635_3 (m.d 2 3) (by simp) with h3682 | h3682
                          · linarith only [h3627, h3682, hlam]
                          · linarith only [h2893, h3682, hlam]
                      · linarith only [h0, h3679, hlam]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h2893, hc12, hc25, hlam, hphi, p3635_1]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [h3633, hlam, p3635_1]
                    · have p3635_0 := h3635c.1
                      have p3635_1 := h3635c.2.1
                      have p3635_2 := h3635c.2.2.1
                      have p3635_3 := h3635c.2.2.2
                      linarith only [hlam, p3635_0]
                  · linarith only [h2, h2893, h3634, h5, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h2892, h3356, h3633, h5, hc12, hc34, hlam, hphi, ht23]

end R2N4
