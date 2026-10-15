import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_42S1
import Jsp000404.R1LeavesN7_42S2
import Jsp000404.R1LeavesN7_42S3

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6588000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x1_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1697 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1952 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2086 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h2276 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  rcases m.htr 0 2 5 (by decide) (by decide) with h2857 | h2857
  · rcases m.htr 0 3 4 (by decide) (by decide) with h2858 | h2858
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2859 | h2859
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2860 | h2860
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2861 | h2861
          · linarith only [h2276, h2857, h2861, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2863 | h2863
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2864 | h2864
              · linarith only [h2860, h2861, h2864, hlam]
              · linarith only [h1697, h2858, h2864, hlam]
            · linarith only [h2860, h2863, hc23, hlam, hphi, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2868 | h2868
          · linarith only [h2276, h2860, h2868, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2870 | h2870
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2871 | h2871
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2872 | h2872
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2873 | h2873
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2874 | h2874
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2875 | h2875
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2876 | h2876
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2877 | h2877
                          · rcases h1bigk with h2878c | h2878c | h2878c | h2878c | h2878c | h2878c | h2878c | h2878c | h2878c | h2878c | h2878c | h2878c | h2878c | h2878c | h2878c | h2878c | h2878c | h2878c | h2878c | h2878c | h2878c | h2878c | h2878c | h2878c | h2878c
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [hlam, p2878_0]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [h0, hlam, p2878_0]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [h1697, hlam, p2878_0]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [h1952, hlam, p2878_0]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [h2086, hlam, p2878_0]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [h2868, h2874, hc01, hc23, hlam, hphi, ht12, p2878_1]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [hlam, p2878_0]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [h2860, hlam, p2878_1]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [h2868, hlam, p2878_1]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [h2086, h2868, h2874, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2878_1, u5ehi5]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              rcases p2878_3 (m.d 0 1) (by simp) with h2889 | h2889
                              · linarith only [h2889, hlam, p2878_0]
                              · rcases p2878_3 (m.d 1 2) (by simp) with h2891 | h2891
                                · linarith only [h2860, h2891, hlam]
                                · linarith only [h0, h2891, hlam]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [h0, h2857, h2860, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2878_1, u5ehi7]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [hlam, p2878_0]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [h1952, h2860, hc01, hc23, hlam, hphi, ht12, p2878_1]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [h2086, h2860, hc01, hc23, hlam, hphi, ht12, p2878_1]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              rcases p2878_3 (m.d 0 1) (by simp) with h2898 | h2898
                              · linarith only [h2898, hlam, p2878_0]
                              · rcases p2878_3 (m.d 1 2) (by simp) with h2900 | h2900
                                · linarith only [h2868, h2900, hlam]
                                · linarith only [h0, h2900, hlam]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [h0, h2857, h2875, h2877, hc14, hlam, hphi, ht01, ht0b, ht5b, p2878_1, u5ehi9]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [h2871, hlam, p2878_1]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [hlam, p2878_0]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [h2086, h2868, h2874, hc01, hc23, hlam, hphi, ht12, p2878_1]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2878_1, u5elo1]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [h2870, hlam, p2878_0]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [h2872, hlam, p2878_0]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [h2873, hlam, p2878_0]
                            · have p2878_0 := h2878c.1
                              have p2878_1 := h2878c.2.1
                              have p2878_2 := h2878c.2.2.1
                              have p2878_3 := h2878c.2.2.2
                              linarith only [hlam, p2878_0]
                          · rcases h1bigk with h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c | h2912c
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [hlam, p2912_0]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [h0, hlam, p2912_0]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [h1697, hlam, p2912_0]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [h1952, hlam, p2912_0]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [h2086, hlam, p2912_0]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [h2868, h2874, hc01, hc23, hlam, hphi, ht12, p2912_1]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [hlam, p2912_0]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [h2860, hlam, p2912_1]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [h2868, hlam, p2912_1]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [h2868, h2874, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2912_1, u5ehi6]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              rcases p2912_3 (m.d 0 1) (by simp) with h2923 | h2923
                              · linarith only [h2923, hlam, p2912_0]
                              · rcases p2912_3 (m.d 1 2) (by simp) with h2925 | h2925
                                · linarith only [h2860, h2925, hlam]
                                · linarith only [h0, h2925, hlam]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [h0, h2857, h2860, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2912_1, u5ehi7]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [hlam, p2912_0]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [h1952, h2860, hc01, hc23, hlam, hphi, ht12, p2912_1]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [h2086, h2860, hc01, hc23, hlam, hphi, ht12, p2912_1]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              rcases p2912_3 (m.d 0 1) (by simp) with h2932 | h2932
                              · linarith only [h2932, hlam, p2912_0]
                              · rcases p2912_3 (m.d 1 2) (by simp) with h2934 | h2934
                                · linarith only [h2868, h2934, hlam]
                                · linarith only [h0, h2934, hlam]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [h0, h2857, h2876, h2877, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p2912_1]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [h2871, hlam, p2912_1]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [hlam, p2912_0]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [h2086, h2860, h2871, hc01, hc23, hlam, hphi, ht12, p2912_1]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2912_1, u5elo1]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [h2870, hlam, p2912_0]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [h2872, hlam, p2912_0]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [h2873, hlam, p2912_0]
                            · have p2912_0 := h2912c.1
                              have p2912_1 := h2912c.2.1
                              have p2912_2 := h2912c.2.2.1
                              have p2912_3 := h2912c.2.2.2
                              linarith only [hlam, p2912_0]
                        · linarith only [h0, h2857, h2868, h2875, h2876, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi8]
                      · linarith only [h1697, h2860, h2875, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
                    · linarith only [h0, h2857, h2860, h2874, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                  · linarith only [h1952, h2276, h2857, h2859, h2873, hlam, hphi, u5ehi7, u5elo0]
                · linarith only [h1952, h2276, h2857, h2871, h2872, hlam, hphi, u5ehi7, u5elo3]
              · linarith only [h1697, h2858, h2871, hlam]
            · linarith only [h0, h2857, h2870, hlam]
      · linarith only [h2276, h2857, h2859, hlam, hphi, u5ehi7, u5elo4]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h2954 | h2954
      · rcases m.htr 1 2 3 (by decide) (by decide) with h2955 | h2955
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2956 | h2956
          · linarith only [h2276, h2857, h2956, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2958 | h2958
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2959 | h2959
              · linarith only [h1697, h2858, h2955, h2956, h2959, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2961 | h2961
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2962 | h2962
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2963 | h2963
                    · linarith only [h2955, h2956, h2959, h2963, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2965 | h2965
                      · linarith only [h2955, h2956, h2963, h2965, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi8]
                      · linarith only [h2955, h2956, h2961, h2963, h2965, hc23, hc34, hlam, hphi]
                  · linarith only [h2955, h2956, h2961, h2962, hlam, hphi, u5ehi8, u5elo4]
                · linarith only [h1697, h2961, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h0, h2857, h2958, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h2971 | h2971
          · linarith only [h2276, h2857, h2971, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi7]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h2973 | h2973
            · rcases m.htr 1 3 4 (by decide) (by decide) with h2974 | h2974
              · rcases m.htr 1 3 5 (by decide) (by decide) with h2975 | h2975
                · rcases m.htr 1 4 5 (by decide) (by decide) with h2976 | h2976
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h2977 | h2977
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h2978 | h2978
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h2979 | h2979
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h2980 | h2980
                          · rcases h1bigk with h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c | h2981c
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [hlam, p2981_0]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [h0, hlam, p2981_0]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [h1697, hlam, p2981_0]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [h1952, hlam, p2981_0]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [h2086, hlam, p2981_0]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [h2971, h2977, hc01, hc23, hlam, hphi, ht12, p2981_1]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [hlam, p2981_0]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [h2955, hlam, p2981_1]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [h2971, hlam, p2981_1]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [h2086, h2971, h2977, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2981_1, u5ehi5]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              rcases p2981_3 (m.d 0 1) (by simp) with h2992 | h2992
                              · linarith only [h2992, hlam, p2981_0]
                              · rcases p2981_3 (m.d 1 2) (by simp) with h2994 | h2994
                                · linarith only [h2955, h2994, hlam]
                                · linarith only [h0, h2994, hlam]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [h0, h2955, hc01, hc23, hlam, hphi, ht12, p2981_1]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [hlam, p2981_0]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [h0, h2857, h2955, h2971, h2978, h2980, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p2981_1, u5ehi9]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [h2086, h2955, hc01, hc23, hlam, hphi, ht12, p2981_1]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              rcases p2981_3 (m.d 0 1) (by simp) with h3001 | h3001
                              · linarith only [h3001, hlam, p2981_0]
                              · rcases p2981_3 (m.d 1 2) (by simp) with h3003 | h3003
                                · linarith only [h2971, h3003, hlam]
                                · linarith only [h0, h3003, hlam]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [h0, h2857, h2978, h2980, hc14, hlam, hphi, ht01, ht0b, ht5b, p2981_1, u5ehi9]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [h2974, hlam, p2981_1]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [hlam, p2981_0]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [h2086, h2971, h2977, hc01, hc23, hlam, hphi, ht12, p2981_1]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p2981_1, u5elo1]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [h2973, hlam, p2981_0]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [h2975, hlam, p2981_0]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [h2976, hlam, p2981_0]
                            · have p2981_0 := h2981c.1
                              have p2981_1 := h2981c.2.1
                              have p2981_2 := h2981c.2.2.1
                              have p2981_3 := h2981c.2.2.2
                              linarith only [hlam, p2981_0]
                          · linarith only [h2276, h2857, h2858, h2978, h2980, hlam, hphi, u5ehi8, u5elo4]
                        · linarith only [h2971, h2979, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                      · linarith only [h2276, h2857, h2858, h2955, h2974, h2978, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                    · linarith only [h2955, h2974, h2977, hlam]
                  · linarith only [h1952, h2858, h2954, h2974, h2976, hc01, hc13, hlam, hphi]
                · linarith only [h2276, h2857, h2858, h2974, h2975, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3021 | h3021
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3022 | h3022
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3023 | h3023
                    · linarith only [h2974, h3021, h3023, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi8]
                    · linarith only [h0, h2857, h2955, h3023, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi7]
                  · linarith only [h0, h2857, h2954, h2955, h2974, h3022, hc04, hlam, hphi, ht0b, ht5b, u5ehi7]
                · linarith only [h0, h2857, h2955, h3021, hlam, hphi, u5ehi7, u5elo3]
            · linarith only [h0, h2857, h2973, hlam]
      · linarith only [h2276, h2857, h2954, hlam, hphi, u5ehi7, u5elo4]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h3030 | h3030
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3031 | h3031
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3032 | h3032
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3033 | h3033
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3034 | h3034
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3035 | h3035
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3036 | h3036
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3037 | h3037
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3038 | h3038
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3039 | h3039
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3040 | h3040
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3041 | h3041
                          · linarith only [h3032, h3038, h3041, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                          · rcases h1bigk with h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c | h3043c
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h0, hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h1697, hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h1952, hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h2086, hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              rcases p3043_3 (m.d 0 1) (by simp) with h3049 | h3049
                              · linarith only [h3049, hlam, p3043_0]
                              · rcases p3043_3 (m.d 1 2) (by simp) with h3051 | h3051
                                · rcases p3043_3 (m.d 1 3) (by simp) with h3052 | h3052
                                  · linarith only [h3032, h3052, hlam]
                                  · linarith only [h1697, h3052, hlam]
                                · linarith only [h3051, hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h1697, hc01, hc12, hlam, hphi, p3043_1]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h0, h2276, h2857, h3031, h3033, h3034, h3041, hc01, hc12, hc34, hlam, hphi, ht45, p3043_1, u5elo1]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h0, h2857, h3034, hc01, hc12, hlam, hphi, p3043_1]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              rcases p3043_3 (m.d 0 1) (by simp) with h3060 | h3060
                              · linarith only [h3060, hlam, p3043_0]
                              · rcases p3043_3 (m.d 1 2) (by simp) with h3062 | h3062
                                · rcases p3043_3 (m.d 1 3) (by simp) with h3063 | h3063
                                  · rcases p3043_3 (m.d 1 4) (by simp) with h3064 | h3064
                                    · linarith only [h3035, h3064, hlam]
                                    · linarith only [h1952, h3064, hlam]
                                  · linarith only [h3063, hlam, p3043_0]
                                · linarith only [h0, h3062, hlam]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h3032, hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h0, h2276, h2857, h3031, h3033, h3034, h3041, hc01, hc13, hc34, hlam, hphi, ht45, p3043_1, u5elo1]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h0, h2857, h3032, h3034, hc01, hc12, hlam, hphi, p3043_1]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              rcases p3043_3 (m.d 0 1) (by simp) with h3073 | h3073
                              · linarith only [h3073, hlam, p3043_0]
                              · rcases p3043_3 (m.d 1 2) (by simp) with h3075 | h3075
                                · rcases p3043_3 (m.d 1 3) (by simp) with h3076 | h3076
                                  · rcases p3043_3 (m.d 1 4) (by simp) with h3077 | h3077
                                    · rcases p3043_3 (m.d 1 5) (by simp) with h3078 | h3078
                                      · linarith only [h3037, h3078, hlam]
                                      · linarith only [h2086, h3078, hlam]
                                    · linarith only [h3077, hlam, p3043_0]
                                  · linarith only [h1697, h3076, hlam]
                                · linarith only [h0, h3075, hlam]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h3033, hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h3035, hlam, p3043_1]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h0, h2857, h3034, hc01, hc14, hlam, hphi, p3043_1]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p3043_1, u5elo1]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h3034, hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h3036, hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [h3037, hlam, p3043_0]
                            · have p3043_0 := h3043c.1
                              have p3043_1 := h3043c.2.1
                              have p3043_2 := h3043c.2.2.1
                              have p3043_3 := h3043c.2.2.2
                              linarith only [hlam, p3043_0]
                        · linarith only [h2276, h3031, h3040, hlam]
                      · linarith only [h2276, h3031, h3038, h3039, hlam, hphi, u5ehi9, u5elo3]
                    · linarith only [h2276, h3030, h3038, hlam]
                  · linarith only [h1952, h2276, h3031, h3037, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h1697, h3030, h3036, hc34, hlam, hphi, ht45, u5elo3]
              · linarith only [h1697, h3030, h3035, hlam]
            · linarith only [h0, h3034, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3100 | h3100
            · linarith only [h2857, h3033, h3100, hc02, hc24, hlam, hphi]
            · linarith only [h1697, h3030, h3031, h3032, h3100, hlam, hphi, u5ehi9, u5elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3103 | h3103
          · linarith only [h0, h2276, h3032, h3103, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3105 | h3105
            · linarith only [h0, h2857, h3032, h3105, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h3105, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3108 | h3108
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3109 | h3109
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3110 | h3110
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3111 | h3111
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3112 | h3112
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3113 | h3113
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3114 | h3114
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3115 | h3115
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3116 | h3116
                        · linarith only [h0, h2276, h3031, h3108, h3114, h3116, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h2276, h3111, h3113, h3116, hc01, hc13, hlam, hphi]
                      · linarith only [h3112, h3114, h3115, hc34, hlam, hphi, ht45, u5elo1]
                    · linarith only [h3030, h3031, h3113, h3114, hc23, hlam, hphi, ht34, ht45, u5elo1]
                  · linarith only [h1952, h3113, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h0, h2276, h3109, h3111, h3112, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · linarith only [h1697, h3030, h3111, hlam]
            · linarith only [h0, h3110, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3125 | h3125
            · linarith only [h0, h2857, h3109, h3125, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h0, h3125, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3128 | h3128
          · linarith only [h0, h2276, h3108, h3128, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3130 | h3130
            · linarith only [h0, h2857, h3108, h3130, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h3130, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h3133 | h3133
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3134 | h3134
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3135 | h3135
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3136 | h3136
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3137 | h3137
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3138 | h3138
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3139 | h3139
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3140 | h3140
                    · linarith only [h3030, h3133, h3134, h3140, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi9]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3142 | h3142
                      · linarith only [h0, h2857, h3136, h3137, h3140, h3142, hc01, hc13, hlam, hphi, u5ehi8, u5elo1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3144 | h3144
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3145 | h3145
                          · rcases h1bigk with h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c | h3146c
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [hlam, p3146_0]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [h0, hlam, p3146_0]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [h1697, hlam, p3146_0]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [h1952, hlam, p3146_0]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [h2086, hlam, p3146_0]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              rcases p3146_3 (m.d 0 1) (by simp) with h3152 | h3152
                              · linarith only [h3152, hlam, p3146_0]
                              · rcases p3146_3 (m.d 1 2) (by simp) with h3154 | h3154
                                · rcases p3146_3 (m.d 1 3) (by simp) with h3155 | h3155
                                  · linarith only [h3134, h3155, hlam]
                                  · linarith only [h1697, h3155, hlam]
                                · linarith only [h3154, hlam, p3146_0]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [hlam, p3146_0]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [h1697, hc01, hc12, hlam, hphi, p3146_1]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [h0, h1952, h2857, h3133, h3138, h3142, hc01, hc12, hlam, hphi, p3146_1, u5ehi9, u5elo1]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [h0, h2857, h3138, h3142, hc01, hc12, hlam, hphi, p3146_1]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              rcases p3146_3 (m.d 0 1) (by simp) with h3163 | h3163
                              · linarith only [h3163, hlam, p3146_0]
                              · rcases p3146_3 (m.d 1 2) (by simp) with h3165 | h3165
                                · rcases p3146_3 (m.d 1 3) (by simp) with h3166 | h3166
                                  · rcases p3146_3 (m.d 1 4) (by simp) with h3167 | h3167
                                    · linarith only [h3137, h3167, hlam]
                                    · linarith only [h1952, h3167, hlam]
                                  · linarith only [h3166, hlam, p3146_0]
                                · linarith only [h0, h3165, hlam]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [h3134, hlam, p3146_0]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [hlam, p3146_0]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [h0, h2276, h2857, h3133, h3137, h3138, h3140, h3142, hc01, hc13, hlam, hphi, p3146_1, u5ehi9, u5elo1]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [h0, h2857, h3134, h3138, h3142, hc01, hc12, hlam, hphi, p3146_1]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              rcases p3146_3 (m.d 0 1) (by simp) with h3176 | h3176
                              · linarith only [h3176, hlam, p3146_0]
                              · rcases p3146_3 (m.d 1 2) (by simp) with h3178 | h3178
                                · rcases p3146_3 (m.d 1 3) (by simp) with h3179 | h3179
                                  · rcases p3146_3 (m.d 1 4) (by simp) with h3180 | h3180
                                    · rcases p3146_3 (m.d 1 5) (by simp) with h3181 | h3181
                                      · linarith only [h3139, h3181, hlam]
                                      · linarith only [h2086, h3181, hlam]
                                    · linarith only [h3180, hlam, p3146_0]
                                  · linarith only [h1697, h3179, hlam]
                                · linarith only [h0, h3178, hlam]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [h3135, hlam, p3146_0]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [h3137, hlam, p3146_1]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [hlam, p3146_0]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [h0, h2857, h3138, h3142, hc01, hc14, hlam, hphi, p3146_1]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p3146_1, u5elo1]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [h3136, hlam, p3146_0]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [h3138, hlam, p3146_0]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [h3139, hlam, p3146_0]
                            · have p3146_0 := h3146c.1
                              have p3146_1 := h3146c.2.1
                              have p3146_2 := h3146c.2.2.1
                              have p3146_3 := h3146c.2.2.2
                              linarith only [hlam, p3146_0]
                          · linarith only [h2276, h3133, h3140, h3145, hlam]
                        · linarith only [h2276, h3133, h3144, hlam]
                  · linarith only [h1952, h2276, h3133, h3139, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h3030, h3133, h3137, h3138, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi9]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3200 | h3200
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3201 | h3201
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3202 | h3202
                    · linarith only [h0, h2857, h3136, h3137, h3200, h3202, hc01, hc23, hlam, hphi, ht12, u5ehi8, u5elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3204 | h3204
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3205 | h3205
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h3206 | h3206
                          · rcases h1bigk with h3207c | h3207c | h3207c | h3207c | h3207c | h3207c | h3207c | h3207c | h3207c | h3207c | h3207c | h3207c | h3207c | h3207c | h3207c | h3207c | h3207c | h3207c | h3207c | h3207c | h3207c | h3207c | h3207c | h3207c | h3207c
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [hlam, p3207_0]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [h0, hlam, p3207_0]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [h1697, hlam, p3207_0]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [h1952, hlam, p3207_0]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [h2086, hlam, p3207_0]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              rcases p3207_3 (m.d 0 1) (by simp) with h3213 | h3213
                              · linarith only [h3213, hlam, p3207_0]
                              · rcases p3207_3 (m.d 1 2) (by simp) with h3215 | h3215
                                · rcases p3207_3 (m.d 1 3) (by simp) with h3216 | h3216
                                  · linarith only [h3134, h3216, hlam]
                                  · linarith only [h1697, h3216, hlam]
                                · linarith only [h3215, hlam, p3207_0]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [hlam, p3207_0]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [h0, h2857, h3134, h3136, h3204, h3206, hc01, hc12, hlam, hphi, p3207_1, u5ehi9, u5elo1]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [h1952, hc01, hc12, hlam, hphi, p3207_1]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [h0, h2857, h3136, hc01, hc12, hlam, hphi, p3207_1]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [h3137, hc01, hc34, hlam, hphi, ht12, ht23, p3207_1]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [h3134, hlam, p3207_0]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [hlam, p3207_0]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [h3137, hlam, p3207_0]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [h0, h2857, h3136, hc01, hc13, hlam, hphi, p3207_1]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              rcases p3207_3 (m.d 0 1) (by simp) with h3229 | h3229
                              · linarith only [h3229, hlam, p3207_0]
                              · rcases p3207_3 (m.d 1 2) (by simp) with h3231 | h3231
                                · rcases p3207_3 (m.d 1 3) (by simp) with h3232 | h3232
                                  · linarith only [h3137, h3232, hlam]
                                  · linarith only [h1697, h3232, hlam]
                                · linarith only [h0, h3231, hlam]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [h3135, hlam, p3207_0]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [h1697, h3137, hc01, hc34, hlam, hphi, ht12, ht23, p3207_1]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [hlam, p3207_0]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [h0, h2857, h3136, h3137, hc01, hc34, hlam, hphi, ht12, ht23, p3207_1]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [hc01, hlam, hphi, ht12, ht23, ht34, ht45, p3207_1, u5elo1]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [h3136, hlam, p3207_0]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [h3200, hlam, p3207_0]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [h3201, hlam, p3207_0]
                            · have p3207_0 := h3207c.1
                              have p3207_1 := h3207c.2.1
                              have p3207_2 := h3207c.2.2.1
                              have p3207_3 := h3207c.2.2.2
                              linarith only [hlam, p3207_0]
                          · linarith only [h3133, h3134, h3137, h3204, h3206, hc04, hlam, hphi, ht0b, ht5b, u5ehi8]
                        · linarith only [h2276, h3133, h3205, hlam]
                      · linarith only [h3137, h3200, h3204, hc23, hc34, hlam, hphi]
                  · linarith only [h1952, h2276, h3133, h3201, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h1697, h3200, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h2276, h3133, h3135, h3136, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi9]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3251 | h3251
            · linarith only [h0, h2857, h3135, h3251, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h0, h3251, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3254 | h3254
          · linarith only [h0, h2276, h3134, h3254, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3256 | h3256
            · linarith only [h0, h2857, h3134, h3256, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h3256, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h3259 | h3259
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3260 | h3260
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3261 | h3261
            · rcases m.htr 1 3 4 (by decide) (by decide) with h3262 | h3262
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3263 | h3263
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3264 | h3264
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3265 | h3265
                    · linarith only [h1697, h3030, h3259, h3265, hc01, hc12, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3267 | h3267
                      · linarith only [h3262, h3265, h3267, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi8]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3269 | h3269
                        · linarith only [h0, h2276, h3133, h3260, h3269, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h2276, h3264, h3269, hc01, hc14, hlam, hphi]
                  · linarith only [h1952, h3264, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h1697, h3263, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h3274 | h3274
                · rcases m.htr 1 4 5 (by decide) (by decide) with h3275 | h3275
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h3276 | h3276
                    · linarith only [h0, h2276, h3133, h3262, h3274, h3275, h3276, hc01, hc23, hlam, hphi, ht12, u5ehi8, u5elo1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h3278 | h3278
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h3279 | h3279
                        · linarith only [h0, h2276, h3133, h3260, h3279, hc01, hc12, hlam, hphi]
                        · linarith only [h0, h2276, h3275, h3279, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo1]
                      · linarith only [h3262, h3274, h3278, hc23, hc34, hlam, hphi]
                  · linarith only [h1952, h3275, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo4]
                · linarith only [h1697, h3274, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo3]
            · linarith only [h0, h3261, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3286 | h3286
            · linarith only [h0, h2857, h3260, h3286, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h0, h3286, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h3289 | h3289
          · linarith only [h0, h2276, h3259, h3289, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h3291 | h3291
            · linarith only [h0, h2857, h3259, h3291, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h3291, hc01, hlam, hphi, ht12, ht23, ht34, ht45, u5elo2]

set_option maxHeartbeats 6588000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x1_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1697 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1952 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h2086 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  rcases m.htr 0 2 4 (by decide) (by decide) with h2276 | h2276
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x1_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 h0 h1697 h1952 h2086 h2276
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x1_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 h0 h1697 h1952 h2086 h2276

set_option maxHeartbeats 6588000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1697 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1952 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h2086 | h2086
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x1_x1_x1_x0 m hb1 hb2 hb4 hb5 h0 h1697 h1952 h2086
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x1_x1_x1_x1 m hb1 hb2 hb4 hb5 h0 h1697 h1952 h2086

set_option maxHeartbeats 6588000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_M_LR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1697 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h1952 | h1952
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x1_x1_x0 m hb1 hb2 hb4 hb5 h0 h1697 h1952
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x1_x1_x1 m hb1 hb2 hb4 hb5 h0 h1697 h1952

set_option maxHeartbeats 6588000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h1697 | h1697
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x1_x0 m hb1 hb2 hb4 hb5 h0 h1697
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x1_x1 m hb1 hb2 hb4 hb5 h0 h1697

set_option maxHeartbeats 6588000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_M_LR (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x0 m hb1 hb2 hb4 hb5 h0
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_M_LR_x1 m hb1 hb2 hb4 hb5 h0

end R2N4
