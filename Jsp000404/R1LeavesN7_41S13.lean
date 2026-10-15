import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_41S11
import Jsp000404.R1LeavesN7_41S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6700000 in
set_option maxHeartbeats 6700000 in
theorem r1l7_11_13_25_L_I_L_I_M_LR_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1732 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2007 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2155 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2349 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h2893 | h2893
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2894 | h2894
    · rcases m.htr 0 3 5 (by decide) (by decide) with h2895 | h2895
      · rcases m.htr 0 4 5 (by decide) (by decide) with h2896 | h2896
        · rcases m.htr 1 2 3 (by decide) (by decide) with h2897 | h2897
          · linarith only [h2349, h2893, h2897, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h2899 | h2899
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2900 | h2900
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2901 | h2901
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2902 | h2902
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2903 | h2903
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2904 | h2904
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2905 | h2905
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2906 | h2906
                          · linarith only [h2897, h2899, h2906, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2908 | h2908
                            · linarith only [h2904, h2906, h2908, hlam]
                            · rcases h1bigk with h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c | h2910c
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [hlam, p2910_0]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [h0, hlam, p2910_0]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [h1732, hlam, p2910_0]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [h2007, hlam, p2910_0]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [h2155, hlam, p2910_0]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [h2897, hc01, hc23, hlam, hphi, ht12, p2910_1]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [hlam, p2910_0]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [h2897, hlam, p2910_0]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [h2007, h2897, hc01, hc23, hlam, hphi, ht12, p2910_1]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [h2155, h2897, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2910_1, u5ehi5]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                rcases p2910_3 (m.d 0 1) (by simp) with h2921 | h2921
                                · linarith only [h2921, hlam, p2910_0]
                                · rcases p2910_3 (m.d 1 2) (by simp) with h2923 | h2923
                                  · linarith only [h2897, h2923, hlam]
                                  · linarith only [h0, h2923, hlam]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [h0, hc01, hc13, hlam, hphi, p2910_1]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [hlam, p2910_0]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [h2007, h2896, h2897, h2904, h2906, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2910_1]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [h2155, h2897, hc01, hc23, hlam, hphi, ht12, p2910_1]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [h2897, h2899, hc01, hc23, hlam, hphi, ht12, p2910_1]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [h2899, hlam, p2910_1]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [h2901, hlam, p2910_0]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [hlam, p2910_0]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [h2155, h2897, h2899, hc01, hc23, hlam, hphi, ht12, p2910_1]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2910_1, u5elo1]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [h2900, hlam, p2910_1]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [h2902, hlam, p2910_0]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [h2903, hlam, p2910_0]
                              · have p2910_0 := h2910c.1
                                have p2910_1 := h2910c.2.1
                                have p2910_2 := h2910c.2.2.1
                                have p2910_3 := h2910c.2.2.2
                                linarith only [hlam, p2910_0]
                        · linarith only [h0, h2893, h2897, h2905, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h2007, h2896, h2897, h2899, h2904, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
                    · linarith only [h2007, h2896, h2903, hlam]
                  · linarith only [h1732, h2902, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · linarith only [h1732, h2894, h2901, hlam]
              · linarith only [h0, h2900, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h2946 | h2946
              · rcases m.htr 1 3 4 (by decide) (by decide) with h2947 | h2947
                · rcases m.htr 1 3 5 (by decide) (by decide) with h2948 | h2948
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h2949 | h2949
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h2950 | h2950
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h2951 | h2951
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h2952 | h2952
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h2953 | h2953
                            · rcases h1bigk with h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c | h2954c
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [hlam, p2954_0]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [h0, hlam, p2954_0]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [h1732, hlam, p2954_0]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [h2007, hlam, p2954_0]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [h2155, hlam, p2954_0]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [h2899, h2950, hc01, hc23, hlam, hphi, ht12, p2954_1]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [hlam, p2954_0]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [h2897, hlam, p2954_0]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [h2899, hlam, p2954_0]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [h2899, h2950, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2954_1, u5ehi6]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                rcases p2954_3 (m.d 0 1) (by simp) with h2965 | h2965
                                · linarith only [h2965, hlam, p2954_0]
                                · rcases p2954_3 (m.d 1 2) (by simp) with h2967 | h2967
                                  · linarith only [h2897, h2967, hlam]
                                  · linarith only [h0, h2967, hlam]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [h0, h2893, h2897, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2954_1, u5ehi7]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [hlam, p2954_0]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [h0, h2893, h2897, h2899, h2951, h2953, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2954_1, u5ehi9]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [h2155, h2897, hc01, hc23, hlam, hphi, ht12, p2954_1]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                rcases p2954_3 (m.d 0 1) (by simp) with h2974 | h2974
                                · linarith only [h2974, hlam, p2954_0]
                                · rcases p2954_3 (m.d 1 2) (by simp) with h2976 | h2976
                                  · linarith only [h2899, h2976, hlam]
                                  · linarith only [h0, h2976, hlam]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [h0, h2893, h2951, h2953, hc14, hlam, hphi, ht01, ht0b, ht5b, p2954_1, u5ehi9]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [h2947, hlam, p2954_0]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [hlam, p2954_0]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [h2155, h2897, h2947, hc01, hc23, hlam, hphi, ht12, p2954_1]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2954_1, u5elo1]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [h2946, hlam, p2954_1]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [h2948, hlam, p2954_0]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [h2949, hlam, p2954_0]
                              · have p2954_0 := h2954c.1
                                have p2954_1 := h2954c.2.1
                                have p2954_2 := h2954c.2.2.1
                                have p2954_3 := h2954c.2.2.2
                                linarith only [hlam, p2954_0]
                            · rcases h1bigk with h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c | h2988c
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [hlam, p2988_0]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [h0, hlam, p2988_0]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [h1732, hlam, p2988_0]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [h2007, hlam, p2988_0]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [h2155, hlam, p2988_0]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [h2899, h2950, hc01, hc23, hlam, hphi, ht12, p2988_1]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [hlam, p2988_0]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [h2897, hlam, p2988_0]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [h2899, hlam, p2988_0]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [h2155, h2899, h2950, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2988_1, u5ehi5]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                rcases p2988_3 (m.d 0 1) (by simp) with h2999 | h2999
                                · linarith only [h2999, hlam, p2988_0]
                                · rcases p2988_3 (m.d 1 2) (by simp) with h3001 | h3001
                                  · linarith only [h2897, h3001, hlam]
                                  · linarith only [h0, h3001, hlam]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [h0, h2893, h2897, h2952, h2953, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p2988_1]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [hlam, p2988_0]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [h2007, h2897, hc01, hc23, hlam, hphi, ht12, p2988_1]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [h2155, h2897, hc01, hc23, hlam, hphi, ht12, p2988_1]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                rcases p2988_3 (m.d 0 1) (by simp) with h3008 | h3008
                                · linarith only [h3008, hlam, p2988_0]
                                · rcases p2988_3 (m.d 1 2) (by simp) with h3010 | h3010
                                  · linarith only [h2899, h3010, hlam]
                                  · linarith only [h0, h3010, hlam]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [h0, h2893, h2952, h2953, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2988_1]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [h2947, hlam, p2988_0]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [hlam, p2988_0]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [h2155, h2897, h2947, hc01, hc23, hlam, hphi, ht12, p2988_1]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2988_1, u5elo1]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [h2946, hlam, p2988_1]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [h2948, hlam, p2988_0]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [h2949, hlam, p2988_0]
                              · have p2988_0 := h2988c.1
                                have p2988_1 := h2988c.2.1
                                have p2988_2 := h2988c.2.2.1
                                have p2988_3 := h2988c.2.2.2
                                linarith only [hlam, p2988_0]
                          · linarith only [h0, h2893, h2896, h2899, h2951, h2952, hc04, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · linarith only [h0, h2893, h2899, h2950, h2951, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                      · linarith only [h2349, h2893, h2950, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h2007, h2155, h2896, h2949, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                  · linarith only [h1732, h2155, h2895, h2948, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                · linarith only [h0, h2893, h2894, h2897, h2947, hc03, hlam, hphi, ht0b, ht5b, u5ehi7]
              · linarith only [h0, h2893, h2946, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3029 | h3029
          · linarith only [h2349, h2893, h3029, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3031 | h3031
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3032 | h3032
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3033 | h3033
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3034 | h3034
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3035 | h3035
                    · linarith only [h2007, h2896, h3029, h3031, h3035, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h2007, h3035, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1732, h2155, h2895, h3034, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                · linarith only [h2894, h2896, h3029, h3033, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
              · linarith only [h0, h2893, h3032, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3041 | h3041
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3042 | h3042
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3043 | h3043
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3044 | h3044
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3045 | h3045
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3046 | h3046
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3047 | h3047
                          · linarith only [h0, h2007, h2893, h2896, h3031, h3045, h3047, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h0, h2893, h3031, h3042, h3044, h3046, h3047, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                        · linarith only [h0, h2007, h2893, h2896, h3031, h3044, h3045, h3046, hc01, hc35, hlam, hphi, ht12, ht23, u5ehi7, u5elo1]
                      · linarith only [h1732, h2894, h2896, h3029, h3044, h3045, hc03, hlam, hphi, ht34, ht45, u5elo1]
                    · linarith only [h0, h2893, h3031, h3044, hlam, hphi, u5ehi7, u5elo4]
                  · linarith only [h0, h2893, h2895, h3031, h3042, h3043, hc03, hlam, hphi, ht0b, ht5b, u5ehi7]
                · linarith only [h1732, h2894, h2896, h3042, hc03, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h0, h2893, h3041, hlam]
      · linarith only [h2349, h2893, h2895, hlam, hphi, u5ehi7, u5elo3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3057 | h3057
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3058 | h3058
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3059 | h3059
          · linarith only [h2349, h2893, h3059, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3061 | h3061
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3062 | h3062
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3063 | h3063
                · linarith only [h2349, h2893, h2894, h3063, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · linarith only [h3059, h3061, h3063, hlam]
              · linarith only [h2007, h2349, h2893, h2894, h3061, h3062, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3067 | h3067
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3068 | h3068
                · linarith only [h2349, h2893, h2894, h3068, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3070 | h3070
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3071 | h3071
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3072 | h3072
                      · linarith only [h1732, h3068, h3072, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h2349, h2893, h3072, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h1732, h2349, h2893, h3058, h3068, h3071, hc04, hlam, hphi, ht0b, ht5b, u5ehi7]
                  · linarith only [h1732, h3057, h3070, hlam]
              · linarith only [h0, h1732, h2349, h2893, h3067, hc01, hc13, hlam, hphi]
        · linarith only [h2349, h2893, h2894, h3058, hlam, hphi, u5ehi7, u5elo4]
      · linarith only [h2349, h2893, h3057, hlam, hphi, u5ehi7, u5elo3]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3080 | h3080
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3081 | h3081
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3082 | h3082
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3083 | h3083
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3084 | h3084
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3085 | h3085
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3086 | h3086
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3087 | h3087
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3088 | h3088
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3089 | h3089
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3090 | h3090
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3091 | h3091
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3092 | h3092
                            · linarith only [h2349, h3080, h3083, h3092, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                            · rcases h1bigk with h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c | h3094c
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h0, hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h1732, hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h2007, hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h2155, hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                rcases p3094_3 (m.d 0 1) (by simp) with h3100 | h3100
                                · linarith only [h3100, hlam, p3094_0]
                                · rcases p3094_3 (m.d 1 2) (by simp) with h3102 | h3102
                                  · rcases p3094_3 (m.d 1 3) (by simp) with h3103 | h3103
                                    · linarith only [h3083, h3103, hlam]
                                    · linarith only [h1732, h3103, hlam]
                                  · linarith only [h3102, hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h1732, hc01, hc12, hlam, hphi, p3094_1]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h2007, hc01, hc12, hlam, hphi, p3094_1]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h0, h2893, h3085, hc01, hc12, hlam, hphi, p3094_1]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                rcases p3094_3 (m.d 0 1) (by simp) with h3111 | h3111
                                · linarith only [h3111, hlam, p3094_0]
                                · rcases p3094_3 (m.d 1 2) (by simp) with h3113 | h3113
                                  · rcases p3094_3 (m.d 1 3) (by simp) with h3114 | h3114
                                    · rcases p3094_3 (m.d 1 4) (by simp) with h3115 | h3115
                                      · linarith only [h3086, h3115, hlam]
                                      · linarith only [h2007, h3115, hlam]
                                    · linarith only [h3114, hlam, p3094_0]
                                  · linarith only [h0, h3113, hlam]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h3083, hlam, p3094_1]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h0, h2007, h2893, h3082, h3085, h3092, hc01, hc13, hc34, hlam, hphi, ht45, p3094_1, u5elo1]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h0, h2893, h3083, h3085, hc01, hc12, hlam, hphi, p3094_1]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                rcases p3094_3 (m.d 0 1) (by simp) with h3124 | h3124
                                · linarith only [h3124, hlam, p3094_0]
                                · rcases p3094_3 (m.d 1 2) (by simp) with h3126 | h3126
                                  · rcases p3094_3 (m.d 1 3) (by simp) with h3127 | h3127
                                    · rcases p3094_3 (m.d 1 4) (by simp) with h3128 | h3128
                                      · rcases p3094_3 (m.d 1 5) (by simp) with h3129 | h3129
                                        · linarith only [h3088, h3129, hlam]
                                        · linarith only [h2155, h3129, hlam]
                                      · linarith only [h3128, hlam, p3094_0]
                                    · linarith only [h1732, h3127, hlam]
                                  · linarith only [h0, h3126, hlam]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h3084, hlam, p3094_1]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h3086, hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h0, h2893, h3085, hc01, hc14, hlam, hphi, p3094_1]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p3094_1, u5elo1]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h3085, hlam, p3094_1]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h3087, hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [h3088, hlam, p3094_0]
                              · have p3094_0 := h3094c.1
                                have p3094_1 := h3094c.2.1
                                have p3094_2 := h3094c.2.2.1
                                have p3094_3 := h3094c.2.2.2
                                linarith only [hlam, p3094_0]
                          · linarith only [h0, h2349, h2893, h3080, h3082, h3083, h3091, hc01, hc12, hlam, hphi]
                        · linarith only [h2349, h3080, h3082, h3090, hlam, hphi, u5ehi9, u5elo3]
                      · linarith only [h2349, h3080, h3089, hlam]
                    · linarith only [h2007, h3088, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1732, h2349, h3081, h3083, h3087, hc01, hc12, hlam, hphi]
                · linarith only [h2349, h3080, h3083, h3086, hlam]
              · linarith only [h2349, h3081, h3083, h3085, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
            · linarith only [h2349, h3080, h3082, h3083, h3084, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3152 | h3152
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3153 | h3153
              · linarith only [h0, h2893, h3083, h3153, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h3152, h3153, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3156 | h3156
              · linarith only [h0, h2893, h3152, h3156, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h3156, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3159 | h3159
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3160 | h3160
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3161 | h3161
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3162 | h3162
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3163 | h3163
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3164 | h3164
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3165 | h3165
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3166 | h3166
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3167 | h3167
                          · linarith only [h2007, h3082, h3159, h3165, h3167, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3169 | h3169
                            · linarith only [h3080, h3082, h3169, hlam]
                            · rcases h1bigk with h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c | h3171c
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h0, hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h1732, hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h2007, hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h2155, hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                rcases p3171_3 (m.d 0 1) (by simp) with h3177 | h3177
                                · linarith only [h3177, hlam, p3171_0]
                                · rcases p3171_3 (m.d 1 2) (by simp) with h3179 | h3179
                                  · rcases p3171_3 (m.d 1 3) (by simp) with h3180 | h3180
                                    · linarith only [h3159, h3180, hlam]
                                    · linarith only [h1732, h3180, hlam]
                                  · linarith only [h3179, hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h0, h2893, h3162, h3164, h3167, hc01, hc12, hlam, hphi, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h0, h2893, h3164, h3167, hc01, hc12, hlam, hphi, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h0, h2893, h3164, h3167, hc01, hc12, hlam, hphi, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                rcases p3171_3 (m.d 0 1) (by simp) with h3188 | h3188
                                · linarith only [h3188, hlam, p3171_0]
                                · rcases p3171_3 (m.d 1 2) (by simp) with h3190 | h3190
                                  · rcases p3171_3 (m.d 1 3) (by simp) with h3191 | h3191
                                    · rcases p3171_3 (m.d 1 4) (by simp) with h3192 | h3192
                                      · linarith only [h3162, h3192, hlam]
                                      · linarith only [h2007, h3192, hlam]
                                    · linarith only [h3191, hlam, p3171_0]
                                  · linarith only [h0, h3190, hlam]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h3159, hlam, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h0, h2893, h3164, h3167, hc01, hc13, hlam, hphi, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h0, h2893, h3159, h3164, h3167, hc01, hc12, hlam, hphi, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                rcases p3171_3 (m.d 0 1) (by simp) with h3201 | h3201
                                · linarith only [h3201, hlam, p3171_0]
                                · rcases p3171_3 (m.d 1 2) (by simp) with h3203 | h3203
                                  · rcases p3171_3 (m.d 1 3) (by simp) with h3204 | h3204
                                    · rcases p3171_3 (m.d 1 4) (by simp) with h3205 | h3205
                                      · rcases p3171_3 (m.d 1 5) (by simp) with h3206 | h3206
                                        · linarith only [h3164, h3206, hlam]
                                        · linarith only [h2155, h3206, hlam]
                                      · linarith only [h3205, hlam, p3171_0]
                                    · linarith only [h1732, h3204, hlam]
                                  · linarith only [h0, h3203, hlam]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h3160, hlam, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h3162, hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h0, h2893, h3164, h3167, hc01, hc14, hlam, hphi, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p3171_1, u5elo1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h3161, hlam, p3171_1]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h3163, hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [h3164, hlam, p3171_0]
                              · have p3171_0 := h3171c.1
                                have p3171_1 := h3171c.2.1
                                have p3171_2 := h3171c.2.2.1
                                have p3171_3 := h3171c.2.2.2
                                linarith only [hlam, p3171_0]
                        · linarith only [h0, h2349, h3166, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                      · linarith only [h2349, h3080, h3082, h3164, h3165, hc03, hlam, hphi, ht34, ht45, u5elo1]
                    · linarith only [h2007, h3164, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1732, h2349, h3081, h3163, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h2349, h3080, h3082, h3159, h3162, hc03, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h0, h3161, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h2349, h3081, h3159, h3160, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3228 | h3228
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3229 | h3229
              · linarith only [h0, h2893, h3159, h3229, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h3228, h3229, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3232 | h3232
              · linarith only [h0, h2893, h3228, h3232, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h3232, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
      · linarith only [h3080, h3081, hc34, hlam, hphi, ht45, u5elo3]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h3236 | h3236
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3237 | h3237
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3238 | h3238
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3239 | h3239
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3240 | h3240
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3241 | h3241
                · linarith only [h3080, h3236, h3241, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3243 | h3243
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3244 | h3244
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3245 | h3245
                      · linarith only [h1732, h3241, h3245, hc01, hc23, hlam, hphi, ht12]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h3247 | h3247
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h3248 | h3248
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h3249 | h3249
                            · rcases h1bigk with h3250c | h3250c | h3250c | h3250c | h3250c | h3250c | h3250c | h3250c | h3250c | h3250c | h3250c | h3250c | h3250c | h3250c | h3250c | h3250c | h3250c | h3250c | h3250c | h3250c | h3250c | h3250c | h3250c | h3250c | h3250c
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [hlam, p3250_0]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [h0, hlam, p3250_0]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [h1732, hlam, p3250_0]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [h2007, hlam, p3250_0]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [h2155, hlam, p3250_0]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                rcases p3250_3 (m.d 0 1) (by simp) with h3256 | h3256
                                · linarith only [h3256, hlam, p3250_0]
                                · rcases p3250_3 (m.d 1 2) (by simp) with h3258 | h3258
                                  · rcases p3250_3 (m.d 1 3) (by simp) with h3259 | h3259
                                    · linarith only [h3238, h3259, hlam]
                                    · linarith only [h1732, h3259, hlam]
                                  · linarith only [h3258, hlam, p3250_0]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [hlam, p3250_0]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [h0, h2349, h2893, h3236, h3238, h3240, h3249, hc01, hc12, hlam, hphi, p3250_1, u5ehi9, u5elo1]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [h2007, hc01, hc12, hlam, hphi, p3250_1]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [h0, h2893, h3240, hc01, hc12, hlam, hphi, p3250_1]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [h3241, hc01, hc34, hlam, hphi, ht12, ht23, p3250_1]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [h3238, hlam, p3250_1]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [hlam, p3250_0]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [h3241, hlam, p3250_1]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [h0, h2893, h3240, hc01, hc13, hlam, hphi, p3250_1]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                rcases p3250_3 (m.d 0 1) (by simp) with h3272 | h3272
                                · linarith only [h3272, hlam, p3250_0]
                                · rcases p3250_3 (m.d 1 2) (by simp) with h3274 | h3274
                                  · rcases p3250_3 (m.d 1 3) (by simp) with h3275 | h3275
                                    · linarith only [h3241, h3275, hlam]
                                    · linarith only [h1732, h3275, hlam]
                                  · linarith only [h0, h3274, hlam]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [h3239, hlam, p3250_1]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [h1732, h3241, hc01, hc34, hlam, hphi, ht12, ht23, p3250_1]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [hlam, p3250_0]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [h0, h2893, h3240, h3241, hc01, hc34, hlam, hphi, ht12, ht23, p3250_1]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p3250_1, u5elo1]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [h3240, hlam, p3250_1]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [h3243, hlam, p3250_0]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [h3244, hlam, p3250_0]
                              · have p3250_0 := h3250c.1
                                have p3250_1 := h3250c.2.1
                                have p3250_2 := h3250c.2.2.1
                                have p3250_3 := h3250c.2.2.2
                                linarith only [hlam, p3250_0]
                            · linarith only [h2349, h3236, h3238, h3241, h3249, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                          · linarith only [h2349, h2893, h3236, h3237, h3240, h3245, h3248, hlam, hphi, u5ehi8, u5elo1]
                        · linarith only [h2349, h3236, h3247, hlam]
                    · linarith only [h2007, h2893, h3237, h3240, h3244, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                  · linarith only [h2349, h3236, h3238, h3243, hlam]
              · linarith only [h0, h3240, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h2349, h3236, h3238, h3239, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3295 | h3295
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3296 | h3296
              · linarith only [h2893, h3238, h3296, hc02, hc23, hlam, hphi]
              · linarith only [h2007, h3080, h3236, h3295, h3296, hlam, hphi, u5ehi8, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3299 | h3299
              · linarith only [h0, h2893, h3295, h3299, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h3299, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · linarith only [h3080, h3236, h3237, hlam, hphi, u5ehi8, u5elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h3303 | h3303
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3304 | h3304
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3305 | h3305
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3306 | h3306
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3307 | h3307
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3308 | h3308
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3309 | h3309
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3310 | h3310
                      · linarith only [h3080, h3303, h3304, h3310, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                      · linarith only [h0, h2349, h3307, h3310, hc01, hc13, hlam, hphi]
                    · linarith only [h2007, h3309, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1732, h3308, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3315 | h3315
                  · linarith only [h0, h2349, h3236, h3307, h3315, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h1732, h3315, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h3306, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h2349, h3304, h3305, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3320 | h3320
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3321 | h3321
              · linarith only [h0, h2893, h3304, h3321, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h3320, h3321, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3324 | h3324
              · linarith only [h0, h2893, h3320, h3324, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h3324, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h3327 | h3327
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3328 | h3328
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3329 | h3329
              · rcases m.htr 1 3 4 (by decide) (by decide) with h3330 | h3330
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3331 | h3331
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h3332 | h3332
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h3333 | h3333
                      · linarith only [h0, h2349, h3080, h3327, h3333, hc01, hc12, hlam, hphi]
                      · linarith only [h0, h2349, h3330, h3333, hc01, hc13, hlam, hphi]
                    · linarith only [h2007, h3332, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1732, h3331, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h3338 | h3338
                  · linarith only [h0, h2349, h3236, h3330, h3338, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h1732, h3338, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h0, h3329, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
            · linarith only [h0, h2349, h3327, h3328, hc01, hc24, hlam, hphi, ht12]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h3343 | h3343
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3344 | h3344
              · linarith only [h0, h2893, h3327, h3344, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h3343, h3344, hc24, hlam, hphi, ht45, u5elo2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h3347 | h3347
              · linarith only [h0, h2893, h3343, h3347, hc01, hc24, hlam, hphi, ht12]
              · linarith only [h0, h3347, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

set_option maxHeartbeats 6700000 in
set_option maxHeartbeats 6700000 in
theorem r1l7_11_13_25_L_I_L_I_M_LR_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1732 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2007 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2155 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h2349 | h2349
  · exact r1l7_11_13_25_L_I_L_I_M_LR_x1_x1_x1_x1_x0 m hb1 hb3 hb5 h0 h1732 h2007 h2155 h2349
  · exact r1l7_11_13_25_L_I_L_I_M_LR_x1_x1_x1_x1_x1 m hb1 hb3 hb5 h0 h1732 h2007 h2155 h2349

set_option maxHeartbeats 6700000 in
set_option maxHeartbeats 6700000 in
theorem r1l7_11_13_25_L_I_L_I_M_LR_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1732 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h2007 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h2155 | h2155
  · exact r1l7_11_13_25_L_I_L_I_M_LR_x1_x1_x1_x0 m hb1 hb3 hb5 h0 h1732 h2007 h2155
  · exact r1l7_11_13_25_L_I_L_I_M_LR_x1_x1_x1_x1 m hb1 hb3 hb5 h0 h1732 h2007 h2155

set_option maxHeartbeats 6700000 in
set_option maxHeartbeats 6700000 in
theorem r1l7_11_13_25_L_I_L_I_M_LR_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1732 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2007 | h2007
  · exact r1l7_11_13_25_L_I_L_I_M_LR_x1_x1_x0 m hb1 hb3 hb5 h0 h1732 h2007
  · exact r1l7_11_13_25_L_I_L_I_M_LR_x1_x1_x1 m hb1 hb3 hb5 h0 h1732 h2007

set_option maxHeartbeats 6700000 in
set_option maxHeartbeats 6700000 in
theorem r1l7_11_13_25_L_I_L_I_M_LR_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1732 | h1732
  · exact r1l7_11_13_25_L_I_L_I_M_LR_x1_x0 m hb1 hb3 hb5 h0 h1732
  · exact r1l7_11_13_25_L_I_L_I_M_LR_x1_x1 m hb1 hb3 hb5 h0 h1732

set_option maxHeartbeats 6700000 in
set_option maxHeartbeats 6700000 in
theorem r1l7_11_13_25_L_I_L_I_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5elo := hb5.1
  have h5ehi := hb5.2.2.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have u5ehi5 := h5ehi (m.d 0 5) (by simp)
  have u5ehi6 := h5ehi (m.d 1 5) (by simp)
  have u5ehi7 := h5ehi (m.d 2 5) (by simp)
  have u5ehi8 := h5ehi (m.d 3 5) (by simp)
  have u5ehi9 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_13_25_L_I_L_I_M_LR_x0 m hb1 hb3 hb5 h0
  · exact r1l7_11_13_25_L_I_L_I_M_LR_x1 m hb1 hb3 hb5 h0

end R2N4
