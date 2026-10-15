import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_14S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6312000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h856 | h856
  · rcases m.htr 0 3 4 (by decide) (by decide) with h857 | h857
    · linarith only [h4, h5, h857, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h859 | h859
      · rcases m.htr 0 4 5 (by decide) (by decide) with h860 | h860
        · rcases m.htr 1 2 3 (by decide) (by decide) with h861 | h861
          · rcases m.htr 1 2 4 (by decide) (by decide) with h862 | h862
            · linarith only [h0, h5, h862, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h864 | h864
              · rcases m.htr 1 3 4 (by decide) (by decide) with h865 | h865
                · linarith only [h0, h857, h859, h861, h865, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h867 | h867
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h868 | h868
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h869 | h869
                      · linarith only [h2, h857, h861, h862, h869, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h871 | h871
                        · linarith only [h0, h861, h871, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h1, h867, h871, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h860, h861, h862, h867, h868, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                  · linarith only [h857, h859, h867, hc13, hc34, hlam, hphi]
              · linarith only [h5, h856, h864, hc12, hc24, hlam, hphi]
          · linarith only [h4, h5, h861, hc12, hc24, hlam, hphi]
        · linarith only [h5, h856, h860, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h879 | h879
        · rcases m.htr 1 2 3 (by decide) (by decide) with h880 | h880
          · rcases m.htr 1 2 4 (by decide) (by decide) with h881 | h881
            · linarith only [h0, h5, h881, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h883 | h883
              · rcases m.htr 1 3 4 (by decide) (by decide) with h884 | h884
                · linarith only [h1, h857, h884, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h886 | h886
                  · linarith only [h1, h859, h886, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h888 | h888
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h889 | h889
                      · linarith only [h0, h857, h880, h889, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h891 | h891
                        · linarith only [h1, h859, h880, h891, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h893 | h893
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h894 | h894
                            · rcases h0bigk with h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c | h895c
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [hlam, p895_0]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p895_1, u0elo0]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                rcases p895_3 (m.d 0 1) (by simp) with h898 | h898
                                · rcases p895_3 (m.d 0 2) (by simp) with h899 | h899
                                  · linarith only [h0, h899, hlam]
                                  · linarith only [h4, h899, hlam]
                                · linarith only [h1, h898, hlam]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [h0, h5, h883, h891, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p895_1, u0elo0]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                rcases p895_3 (m.d 0 1) (by simp) with h904 | h904
                                · rcases p895_3 (m.d 0 2) (by simp) with h905 | h905
                                  · linarith only [h0, h905, hlam]
                                  · linarith only [h856, h905, hlam]
                                · linarith only [h3, h904, hlam]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [h0, hlam, p895_0]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [hlam, p895_0]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [h1, h5, h880, h889, hc23, hc34, hlam, hphi, p895_1]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [h5, hlam, p895_1]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [h3, h5, h880, h886, h889, hc23, hc34, hlam, hphi, p895_1]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [h1, hlam, p895_1]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [h4, hlam, p895_1]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [hlam, p895_0]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [h857, hlam, p895_1]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [h859, hlam, p895_1]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [h2, hlam, p895_0]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [h0, h883, h891, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p895_1, u0elo3]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                rcases p895_3 (m.d 0 1) (by simp) with h921 | h921
                                · rcases p895_3 (m.d 0 2) (by simp) with h922 | h922
                                  · linarith only [h5, h922, hlam]
                                  · linarith only [h4, h922, hlam]
                                · linarith only [h1, h921, hlam]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [hlam, p895_0]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                rcases p895_3 (m.d 0 1) (by simp) with h927 | h927
                                · rcases p895_3 (m.d 0 2) (by simp) with h928 | h928
                                  · linarith only [h5, h928, hlam]
                                  · linarith only [h856, h928, hlam]
                                · linarith only [h3, h927, hlam]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [h3, hlam, p895_0]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [h856, hlam, p895_1]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [h1, h5, h856, h880, h889, hc23, hc34, hlam, hphi, p895_1]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [h879, hlam, p895_1]
                              · have p895_0 := h895c.1
                                have p895_1 := h895c.2.1
                                have p895_2 := h895c.2.2.1
                                have p895_3 := h895c.2.2.2
                                linarith only [hlam, p895_0]
                            · linarith only [h0, h5, h883, h889, h893, h894, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h3, h5, h888, h893, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h2, h879, h880, h881, h888, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
              · linarith only [h5, h856, h880, h883, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
          · linarith only [h4, h5, h880, hc12, hc24, hlam, hphi]
        · linarith only [h5, h856, h879, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h943 | h943
    · linarith only [h4, h5, h943, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h945 | h945
      · linarith only [h4, h856, h945, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h947 | h947
        · rcases m.htr 1 2 3 (by decide) (by decide) with h948 | h948
          · rcases m.htr 1 2 4 (by decide) (by decide) with h949 | h949
            · linarith only [h0, h5, h949, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h951 | h951
              · linarith only [h0, h856, h951, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h953 | h953
                · linarith only [h1, h943, h953, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h955 | h955
                  · linarith only [h0, h1, h856, h945, h948, h955, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h957 | h957
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h958 | h958
                      · linarith only [h0, h943, h948, h958, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h960 | h960
                        · linarith only [h2, h945, h948, h951, h957, h960, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h962 | h962
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h963 | h963
                            · rcases h0bigk with h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c | h964c
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [hlam, p964_0]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [h4, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p964_1, u0elo0]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                rcases p964_3 (m.d 0 1) (by simp) with h967 | h967
                                · rcases p964_3 (m.d 0 2) (by simp) with h968 | h968
                                  · linarith only [h0, h968, hlam]
                                  · linarith only [h4, h968, hlam]
                                · linarith only [h1, h967, hlam]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [h0, h856, h947, h948, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p964_1, u0elo0]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [h0, h856, h948, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p964_1, u0elo0]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [h0, hlam, p964_0]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [hlam, p964_0]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [h1, h856, h948, h958, h962, hc23, hc34, hlam, hphi, p964_1]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [h5, hlam, p964_1]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [h856, hlam, p964_0]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [h1, hlam, p964_1]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [h4, hlam, p964_1]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [hlam, p964_0]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [h943, hlam, p964_1]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [h945, hlam, p964_1]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [h2, hlam, p964_0]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [h0, h948, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p964_1, u0elo3]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                rcases p964_3 (m.d 0 1) (by simp) with h986 | h986
                                · rcases p964_3 (m.d 0 2) (by simp) with h987 | h987
                                  · linarith only [h5, h987, hlam]
                                  · linarith only [h4, h987, hlam]
                                · linarith only [h1, h986, hlam]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [hlam, p964_0]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [h0, h2, h856, h948, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p964_1, u0elo0]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [h3, hlam, p964_0]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [h0, h948, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p964_1, u0elo4]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                rcases p964_3 (m.d 0 1) (by simp) with h995 | h995
                                · rcases p964_3 (m.d 0 2) (by simp) with h996 | h996
                                  · linarith only [h856, h996, hlam]
                                  · linarith only [h4, h996, hlam]
                                · linarith only [h1, h995, hlam]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [h947, hlam, p964_1]
                              · have p964_0 := h964c.1
                                have p964_1 := h964c.2.1
                                have p964_2 := h964c.2.2.1
                                have p964_3 := h964c.2.2.2
                                linarith only [hlam, p964_0]
                            · linarith only [h0, h5, h948, h958, h963, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h2, h5, h957, h962, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · linarith only [h947, h948, h949, h957, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
          · linarith only [h4, h856, h948, hc12, hc25, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1006 | h1006
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1007 | h1007
            · linarith only [h0, h1007, h5, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1009 | h1009
              · linarith only [h0, h1009, h856, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1011 | h1011
                · linarith only [h1, h1006, h1007, h1011, h2, h943, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1013 | h1013
                  · linarith only [h1, h1013, h945, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1015 | h1015
                    · linarith only [h1015, h2, h947, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1017 | h1017
                      · linarith only [h0, h1006, h1017, h943, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1019 | h1019
                        · linarith only [h1007, h1019, h2, h4, h5, h945, h947, hc12, hc24, hlam, hphi]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1021 | h1021
                          · linarith only [h0, h1006, h1017, h1021, h5, h947, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h1006, h1021, h5, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h1006, h4, h5, hc12, hc24, hlam, hphi]

set_option maxHeartbeats 6312000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5

set_option maxHeartbeats 6312000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1025 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h1026 | h1026
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1027 | h1027
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1028 | h1028
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1029 | h1029
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1030 | h1030
          · linarith only [h0, h1025, h1030, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1032 | h1032
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1033 | h1033
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1034 | h1034
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1035 | h1035
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1036 | h1036
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1037 | h1037
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1038 | h1038
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1039 | h1039
                          · linarith only [h0, h1032, h1039, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h1, h1030, h1032, h1036, h1037, h1039, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1, h1028, h1038, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h1027, h1037, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1044 | h1044
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1045 | h1045
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1046 | h1046
                          · linarith only [h1032, h1036, h1046, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1048 | h1048
                            · linarith only [h1032, h1036, h1044, h1048, hlam]
                            · rcases h0bigk with h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [hlam, p1050_0]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h1025, h1029, h1032, h1036, h1044, hc34, hlam, hphi, ht0b, ht45, ht5b, p1050_1, u0elo0]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h1, h1030, h1033, h1044, h1046, hc34, hlam, hphi, ht0b, ht45, ht5b, p1050_1, u0elo0]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h1029, h1032, h1036, h1044, hc34, hlam, hphi, ht0b, ht45, ht5b, p1050_1, u0elo0]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h1029, h1032, h1036, h1044, hc34, hlam, hphi, ht0b, ht45, ht5b, p1050_1, u0elo0]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h0, hlam, p1050_0]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [hlam, p1050_0]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h4, hlam, p1050_0]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h1029, h1032, h1036, h1044, hc34, hlam, hphi, ht0b, ht45, ht5b, p1050_1, u0elo1]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h1029, h1032, h1036, h1044, hc34, hlam, hphi, ht0b, ht45, ht5b, p1050_1, u0elo1]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h1, hlam, p1050_1]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h0, h1033, h1044, h1046, hc34, hlam, hphi, ht0b, ht45, ht5b, p1050_1, u0elo2]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [hlam, p1050_0]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h1, h1029, h1032, h1036, h1044, hc34, hlam, hphi, ht0b, ht45, ht5b, p1050_1, u0elo0]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h1, h1029, h1032, h1036, h1044, hc34, hlam, hphi, ht0b, ht45, ht5b, p1050_1, u0elo0]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h2, hlam, p1050_0]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h1025, hlam, p1050_0]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h1027, hlam, p1050_0]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [hlam, p1050_0]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h1025, h1029, h1032, h1036, h1044, hc34, hlam, hphi, ht0b, ht45, ht5b, p1050_1, u0elo1]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h3, hlam, p1050_0]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h1026, hlam, p1050_1]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h1028, hlam, p1050_0]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [h1029, hlam, p1050_1]
                              · have p1050_0 := h1050c.1
                                have p1050_1 := h1050c.2.1
                                have p1050_2 := h1050c.2.2.1
                                have p1050_3 := h1050c.2.2.2
                                linarith only [hlam, p1050_0]
                        · linarith only [h1028, h1045, h4, hlam]
                      · linarith only [h1025, h1029, h1032, h1036, h1044, h4, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · linarith only [h1028, h1030, h1032, h1035, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h1, h1027, h1030, h1032, h1034, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h1026, h1032, h1033, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · linarith only [h1025, h1032, h4, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1082 | h1082
          · linarith only [h0, h1082, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1084 | h1084
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1085 | h1085
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1086 | h1086
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1087 | h1087
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1088 | h1088
                    · linarith only [h1029, h1088, h2, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1090 | h1090
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1091 | h1091
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1092 | h1092
                          · linarith only [h0, h1029, h1084, h1092, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1094 | h1094
                            · linarith only [h1029, h1084, h1090, h1094, h2, hlam]
                            · rcases h0bigk with h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c | h1096c
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h0, h1085, h1090, h1092, hc34, hlam, hphi, ht0b, ht45, ht5b, p1096_1, u0elo0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h1, h1082, h1085, h1090, h1092, hc34, hlam, hphi, ht0b, ht45, ht5b, p1096_1, u0elo0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                rcases p1096_3 (m.d 0 1) (by simp) with h1100 | h1100
                                · rcases p1096_3 (m.d 0 2) (by simp) with h1101 | h1101
                                  · linarith only [h0, h1101, hlam]
                                  · linarith only [h1025, h1101, hlam]
                                · linarith only [h1100, h2, hlam]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                rcases p1096_3 (m.d 0 1) (by simp) with h1105 | h1105
                                · rcases p1096_3 (m.d 0 2) (by simp) with h1106 | h1106
                                  · linarith only [h0, h1106, hlam]
                                  · linarith only [h1026, h1106, hlam]
                                · linarith only [h1105, h3, hlam]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h0, hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h4, hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                rcases p1096_3 (m.d 0 1) (by simp) with h1113 | h1113
                                · rcases p1096_3 (m.d 0 2) (by simp) with h1114 | h1114
                                  · rcases p1096_3 (m.d 0 3) (by simp) with h1115 | h1115
                                    · rcases p1096_3 (m.d 0 4) (by simp) with h1116 | h1116
                                      · linarith only [h1025, h1116, hlam]
                                      · rcases p1096_3 (m.d 0 5) (by simp) with h1118 | h1118
                                        · linarith only [h1026, h1118, hlam]
                                        · linarith only [h1029, h1118, hlam]
                                    · linarith only [h1027, h1115, hlam]
                                  · linarith only [h1025, h1114, hlam]
                                · linarith only [h1113, h2, hlam]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                rcases p1096_3 (m.d 0 1) (by simp) with h1124 | h1124
                                · rcases p1096_3 (m.d 0 2) (by simp) with h1125 | h1125
                                  · rcases p1096_3 (m.d 0 3) (by simp) with h1126 | h1126
                                    · rcases p1096_3 (m.d 0 4) (by simp) with h1127 | h1127
                                      · linarith only [h1025, h1127, hlam]
                                      · rcases p1096_3 (m.d 0 5) (by simp) with h1129 | h1129
                                        · linarith only [h1026, h1129, hlam]
                                        · rcases h2bigk with h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c | h1131c
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [hlam, p1131_0]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [h1085, h1090, h1092, hc34, hlam, hphi, ht0b, ht45, ht5b, p1131_1, u0elo1]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [h4, hlam, p1131_0]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            rcases p1131_3 (m.d 0 2) (by simp) with h1135 | h1135
                                            · rcases p1131_3 (m.d 1 2) (by simp) with h1136 | h1136
                                              · linarith only [h0, h1136, hlam]
                                              · linarith only [h1084, h1136, hlam]
                                            · linarith only [h1135, hlam, p1131_0]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            rcases p1131_3 (m.d 0 2) (by simp) with h1140 | h1140
                                            · rcases p1131_3 (m.d 1 2) (by simp) with h1141 | h1141
                                              · linarith only [h0, h1141, hlam]
                                              · linarith only [h1085, h1141, hlam]
                                            · linarith only [h1140, hlam, p1131_0]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [h0, hlam, p1131_0]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [hlam, p1131_0]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [h1082, hlam, p1131_0]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [h0, h1090, hc34, hlam, hphi, ht0b, ht45, ht5b, p1131_1, u0elo0]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [h1, h1082, h1090, h1092, hc34, hlam, hphi, ht0b, ht45, ht5b, p1131_1, u0elo0]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [h1084, h1088, h1090, h3, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1096_1, p1131_1]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            rcases p1131_3 (m.d 0 2) (by simp) with h1151 | h1151
                                            · linarith only [h1151, h4, hlam]
                                            · linarith only [h0, h1151, hlam]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [hlam, p1131_0]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [h1084, h1088, h3, h4, hlam, p1096_1, p1131_2]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [h1026, h4, hlam, p1096_1, p1131_2]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [h1025, hlam, p1131_0]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [h1084, hlam, p1131_0]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [h1090, hlam, p1131_1]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [hlam, p1131_0]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [h1092, hlam, p1131_1]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [h1026, hlam, p1131_0]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [h1085, hlam, p1131_0]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [h1091, hlam, p1131_1]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [h1085, h1090, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, p1096_1, p1131_1, u0elo1]
                                          · have p1131_0 := h1131c.1
                                            have p1131_1 := h1131c.2.1
                                            have p1131_2 := h1131c.2.2.1
                                            have p1131_3 := h1131c.2.2.2
                                            linarith only [hlam, p1131_0]
                                    · linarith only [h1028, h1126, hlam]
                                  · linarith only [h1026, h1125, hlam]
                                · linarith only [h1124, h3, hlam]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h1, hlam, p1096_1]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h1, h1025, h1090, hc34, hlam, hphi, ht0b, ht45, ht5b, p1096_1, u0elo0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                rcases p1096_3 (m.d 0 1) (by simp) with h1173 | h1173
                                · rcases p1096_3 (m.d 0 2) (by simp) with h1174 | h1174
                                  · linarith only [h1174, h4, hlam]
                                  · linarith only [h1025, h1174, hlam]
                                · linarith only [h1173, h2, hlam]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                rcases p1096_3 (m.d 0 1) (by simp) with h1178 | h1178
                                · rcases p1096_3 (m.d 0 2) (by simp) with h1179 | h1179
                                  · linarith only [h1179, h4, hlam]
                                  · linarith only [h1026, h1179, hlam]
                                · linarith only [h1178, h3, hlam]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h2, hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h1025, hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h1027, hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h1029, hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h3, hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h1026, hlam, p1096_1]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [h1028, hlam, p1096_0]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                rcases p1096_3 (m.d 0 1) (by simp) with h1191 | h1191
                                · rcases p1096_3 (m.d 0 2) (by simp) with h1192 | h1192
                                  · rcases p1096_3 (m.d 0 3) (by simp) with h1193 | h1193
                                    · rcases p1096_3 (m.d 0 4) (by simp) with h1194 | h1194
                                      · linarith only [h1029, h1194, hlam]
                                      · rcases p1096_3 (m.d 0 5) (by simp) with h1196 | h1196
                                        · rcases h2bigk with h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [hlam, p1197_0]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [h1085, h1090, h1092, hc34, hlam, hphi, ht0b, ht45, ht5b, p1197_1, u0elo1]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [h4, hlam, p1197_0]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            rcases p1197_3 (m.d 0 2) (by simp) with h1201 | h1201
                                            · rcases p1197_3 (m.d 1 2) (by simp) with h1202 | h1202
                                              · linarith only [h0, h1202, hlam]
                                              · linarith only [h1084, h1202, hlam]
                                            · linarith only [h1201, hlam, p1197_0]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            rcases p1197_3 (m.d 0 2) (by simp) with h1206 | h1206
                                            · rcases p1197_3 (m.d 1 2) (by simp) with h1207 | h1207
                                              · linarith only [h0, h1207, hlam]
                                              · linarith only [h1085, h1207, hlam]
                                            · linarith only [h1206, hlam, p1197_0]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [h0, hlam, p1197_0]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [hlam, p1197_0]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [h1082, hlam, p1197_0]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [h0, h1090, hc34, hlam, hphi, ht0b, ht45, ht5b, p1197_1, u0elo0]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [h1, h1082, h1090, h1092, hc34, hlam, hphi, ht0b, ht45, ht5b, p1197_1, u0elo0]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [h1026, h1084, h1090, h2, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1096_1, p1197_1]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            rcases p1197_3 (m.d 0 2) (by simp) with h1217 | h1217
                                            · linarith only [h1217, h4, hlam]
                                            · linarith only [h0, h1217, hlam]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [hlam, p1197_0]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [h1026, h1084, h2, h4, hlam, p1096_1, p1197_2]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            rcases p1197_3 (m.d 0 2) (by simp) with h1222 | h1222
                                            · linarith only [h1222, h4, hlam]
                                            · linarith only [h1026, h1222, hlam]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [h1025, hlam, p1197_0]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [h1084, hlam, p1197_0]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [h1090, hlam, p1197_1]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [hlam, p1197_0]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [h1092, hlam, p1197_1]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [h1026, hlam, p1197_0]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [h1085, hlam, p1197_0]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [h1091, hlam, p1197_1]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [h0, h1085, h1090, hc34, hlam, hphi, ht0b, ht45, ht5b, p1197_1, u0elo0]
                                          · have p1197_0 := h1197c.1
                                            have p1197_1 := h1197c.2.1
                                            have p1197_2 := h1197c.2.2.1
                                            have p1197_3 := h1197c.2.2.2
                                            linarith only [hlam, p1197_0]
                                        · linarith only [h1029, h1196, hlam]
                                    · linarith only [h1027, h1193, hlam]
                                  · linarith only [h1025, h1192, hlam]
                                · linarith only [h1191, h2, hlam]
                              · have p1096_0 := h1096c.1
                                have p1096_1 := h1096c.2.1
                                have p1096_2 := h1096c.2.2.1
                                have p1096_3 := h1096c.2.2.2
                                linarith only [hlam, p1096_0]
                        · linarith only [h1028, h1091, h4, hlam]
                      · linarith only [h1027, h1090, h4, hlam]
                  · linarith only [h1, h1028, h1082, h1085, h1087, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h1, h1027, h1082, h1084, h1086, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h1026, h1084, h1085, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · linarith only [h1025, h1084, h4, hc12, hc23, hlam, hphi]
      · linarith only [h1026, h1028, h4, hlam]
    · linarith only [h1025, h1027, h4, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1248 | h1248
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1249 | h1249
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1250 | h1250
        · linarith only [h1025, h1026, h1250, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1252 | h1252
          · linarith only [h0, h1252, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1254 | h1254
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1255 | h1255
              · linarith only [h0, h1026, h1255, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1257 | h1257
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1258 | h1258
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1259 | h1259
                    · linarith only [h1250, h1259, h2, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1261 | h1261
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1262 | h1262
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1263 | h1263
                          · linarith only [h0, h1250, h1254, h1263, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1265 | h1265
                            · linarith only [h1, h1026, h1254, h1255, h1258, h1261, h1263, h1265, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                            · rcases h0bigk with h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [hlam, p1267_0]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [h0, h1254, h1261, hc34, hlam, hphi, ht0b, ht45, ht5b, p1267_1, u0elo0]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [h1, h1258, hc35, hlam, hphi, ht0b, ht5b, p1267_1, u0elo0]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                rcases p1267_3 (m.d 0 1) (by simp) with h1271 | h1271
                                · rcases p1267_3 (m.d 0 2) (by simp) with h1272 | h1272
                                  · linarith only [h0, h1272, hlam]
                                  · linarith only [h1025, h1272, hlam]
                                · linarith only [h1271, h2, hlam]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [h0, h1026, h1254, h1261, hc34, hlam, hphi, ht0b, ht45, ht5b, p1267_1, u0elo0]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [h0, hlam, p1267_0]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [hlam, p1267_0]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [h4, hlam, p1267_0]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [h1026, h1254, h1261, h1263, h2, hc34, hc45, hlam, hphi, p1267_1]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [h1026, hlam, p1267_0]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [h1, hlam, p1267_1]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [h0, h1254, h1261, hc34, hlam, hphi, ht0b, ht45, ht5b, p1267_1, u0elo2]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [hlam, p1267_0]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                rcases p1267_3 (m.d 0 1) (by simp) with h1285 | h1285
                                · rcases p1267_3 (m.d 0 2) (by simp) with h1286 | h1286
                                  · linarith only [h1286, h4, hlam]
                                  · linarith only [h1025, h1286, hlam]
                                · linarith only [h1285, h2, hlam]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [h0, h1, h1026, h1254, h1261, hc34, hlam, hphi, ht0b, ht45, ht5b, p1267_1, u0elo0]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [h2, hlam, p1267_0]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [h1025, hlam, p1267_0]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [h1248, hlam, p1267_0]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [hlam, p1267_0]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [h1250, hlam, p1267_0]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [h3, hlam, p1267_0]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [h0, h1254, h1261, hc34, hlam, hphi, ht0b, ht45, ht5b, p1267_1, u0elo4]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [h1249, hlam, p1267_0]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                rcases p1267_3 (m.d 0 1) (by simp) with h1299 | h1299
                                · rcases p1267_3 (m.d 0 2) (by simp) with h1300 | h1300
                                  · linarith only [h1026, h1300, hlam]
                                  · linarith only [h1025, h1300, hlam]
                                · linarith only [h1299, h2, hlam]
                              · have p1267_0 := h1267c.1
                                have p1267_1 := h1267c.2.1
                                have p1267_2 := h1267c.2.2.1
                                have p1267_3 := h1267c.2.2.2
                                linarith only [hlam, p1267_0]
                        · linarith only [h1249, h1262, h4, hlam]
                      · linarith only [h1248, h1261, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h1, h1249, h1252, h1254, h1258, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h1, h1248, h1252, h1254, h1257, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · linarith only [h1025, h1026, h1254, hc12, hc25, hlam, hphi]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1310 | h1310
        · linarith only [h1025, h1249, h1310, h4, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1312 | h1312
          · linarith only [h0, h1312, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1314 | h1314
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1315 | h1315
              · linarith only [h0, h1026, h1315, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1317 | h1317
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1318 | h1318
                  · linarith only [h1, h1249, h1318, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1320 | h1320
                    · linarith only [h1310, h1320, h2, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1322 | h1322
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1323 | h1323
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1324 | h1324
                          · linarith only [h0, h1310, h1314, h1324, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1326 | h1326
                            · linarith only [h0, h1249, h1314, h1322, h1323, h1324, h1326, h4, hlam]
                            · rcases h0bigk with h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c | h1328c
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [hlam, p1328_0]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [h0, h1314, hc24, hlam, hphi, ht0b, ht45, ht5b, p1328_1, u0elo0]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [h0, h1314, h1322, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, p1328_1, u0elo0]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                rcases p1328_3 (m.d 0 1) (by simp) with h1332 | h1332
                                · rcases p1328_3 (m.d 0 2) (by simp) with h1333 | h1333
                                  · linarith only [h0, h1333, hlam]
                                  · linarith only [h1025, h1333, hlam]
                                · linarith only [h1332, h2, hlam]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [h0, h1026, h1314, h1322, hc34, hlam, hphi, ht0b, ht45, ht5b, p1328_1, u0elo0]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [h0, hlam, p1328_0]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [hlam, p1328_0]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [h4, hlam, p1328_0]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [h1249, h1314, h1322, h1323, h2, h4, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1328_1]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [h1026, hlam, p1328_0]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [h1, hlam, p1328_1]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [h1249, h1323, hc02, hc23, hlam, hphi, p1328_1]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [hlam, p1328_0]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [h1249, h1314, h1322, h1323, h2, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1328_1]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [h1249, hlam, p1328_1]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [h2, hlam, p1328_0]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [h1025, hlam, p1328_0]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [h1248, hlam, p1328_0]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [hlam, p1328_0]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [h1310, hlam, p1328_0]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [h3, hlam, p1328_0]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [h0, h1314, h1322, hc34, hlam, hphi, ht0b, ht45, ht5b, p1328_1, u0elo4]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [h1, h1249, h1312, h1314, h1322, h1323, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1328_1]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                rcases p1328_3 (m.d 0 1) (by simp) with h1356 | h1356
                                · rcases p1328_3 (m.d 0 2) (by simp) with h1357 | h1357
                                  · linarith only [h1026, h1357, hlam]
                                  · linarith only [h1025, h1357, hlam]
                                · linarith only [h1356, h2, hlam]
                              · have p1328_0 := h1328c.1
                                have p1328_1 := h1328c.2.1
                                have p1328_2 := h1328c.2.2.1
                                have p1328_3 := h1328c.2.2.2
                                linarith only [hlam, p1328_0]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1362 | h1362
                          · linarith only [h0, h1314, h1323, h1362, h4, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1364 | h1364
                            · linarith only [h0, h1026, h1314, h1322, h1323, h1362, h1364, h4, hc05, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h0, h1314, h1322, h1323, h1364, h4, hc34, hc45, hlam, hphi]
                      · linarith only [h0, h1248, h1314, h1322, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h1248, h1249, h1312, h1317, hc12, hc35, hlam, hphi, ht23]
            · linarith only [h1025, h1249, h1314, h4, hc12, hc35, hlam, hphi, ht23]
    · linarith only [h1025, h1248, h4, hlam]

set_option maxHeartbeats 6312000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_I_s3_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h1025 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1371 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h1372 | h1372
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1373 | h1373
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1374 | h1374
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1375 | h1375
        · linarith only [h0, h1375, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1377 | h1377
          · linarith only [h0, h1025, h1377, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1379 | h1379
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1380 | h1380
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1381 | h1381
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1382 | h1382
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1383 | h1383
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1384 | h1384
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1385 | h1385
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1386 | h1386
                          · linarith only [h1, h1380, h1386, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h1, h1380, h1382, h1386, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h1, h1025, h1380, h1382, h1385, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h1373, h1384, h4, hlam]
                    · linarith only [h1372, h1383, h4, hlam]
                  · linarith only [h1374, h1377, h1379, h1382, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                · linarith only [h1, h1373, h1380, h1381, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
              · linarith only [h1, h1372, h1375, h1379, h1380, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
            · linarith only [h1025, h1371, h1379, hc12, hc24, hlam, hphi]
      · linarith only [h1025, h1371, h1374, hlam]
    · linarith only [h1371, h1373, h4, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1398 | h1398
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1399 | h1399
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1400 | h1400
        · linarith only [h0, h1400, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1402 | h1402
          · linarith only [h0, h1025, h1402, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1404 | h1404
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1405 | h1405
              · linarith only [h0, h1, h1372, h1404, h1405, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1407 | h1407
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1408 | h1408
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1409 | h1409
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1410 | h1410
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1411 | h1411
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1412 | h1412
                          · rcases h0bigk with h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c | h1413c
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h0, h1404, h1410, h1412, hc45, hlam, hphi, ht0b, ht5b, p1413_1, u0elo0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h0, h1404, h1410, h1412, h4, hc45, hlam, hphi, ht0b, ht5b, p1413_1, u0elo0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h0, h1372, h1404, h1410, h1412, h4, hc45, hlam, hphi, ht0b, ht5b, p1413_1, u0elo0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              rcases p1413_3 (m.d 0 1) (by simp) with h1418 | h1418
                              · rcases p1413_3 (m.d 0 2) (by simp) with h1419 | h1419
                                · linarith only [h0, h1419, hlam]
                                · linarith only [h1371, h1419, hlam]
                              · linarith only [h1418, h3, hlam]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h0, hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h4, hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h1025, hlam, p1413_1]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h1372, h1409, h4, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1413_1]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h1, hlam, p1413_1]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h0, h1372, h1409, hc12, hc23, hlam, hphi, p1413_1]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h1372, hlam, p1413_1]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h1371, h1372, h1409, h1410, h1412, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1413_1]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h2, hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h0, h1404, h1410, h1412, hc45, hlam, hphi, ht0b, ht5b, p1413_1, u0elo3]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h0, h1372, h1404, h1409, h1410, h1412, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1413_1]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              rcases p1413_3 (m.d 0 1) (by simp) with h1437 | h1437
                              · rcases p1413_3 (m.d 0 2) (by simp) with h1438 | h1438
                                · linarith only [h1025, h1438, hlam]
                                · linarith only [h1371, h1438, hlam]
                              · linarith only [h1437, h3, hlam]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h3, hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h1371, hlam, p1413_1]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h1398, hlam, p1413_0]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [h1399, hlam, p1413_1]
                            · have p1413_0 := h1413c.1
                              have p1413_1 := h1413c.2.1
                              have p1413_2 := h1413c.2.2.1
                              have p1413_3 := h1413c.2.2.2
                              linarith only [hlam, p1413_0]
                          · linarith only [h1372, h1399, h1412, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                        · linarith only [h0, h1372, h1404, h1408, h1409, h1410, h1411, h3, h4, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                      · linarith only [h1372, h1398, h1410, hc23, hc34, hlam, hphi]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1450 | h1450
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1451 | h1451
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1452 | h1452
                          · rcases h0bigk with h1453c | h1453c | h1453c | h1453c | h1453c | h1453c | h1453c | h1453c | h1453c | h1453c | h1453c | h1453c | h1453c | h1453c | h1453c | h1453c | h1453c | h1453c | h1453c | h1453c | h1453c | h1453c | h1453c | h1453c | h1453c
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [hlam, p1453_0]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [h0, h1404, hc25, hlam, hphi, ht0b, ht5b, p1453_1, u0elo0]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [h1, h1400, h1404, h1450, h1452, hc45, hlam, hphi, ht0b, ht5b, p1453_1, u0elo0]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [h1400, h1404, h1405, h1450, h1452, h2, hc45, hlam, hphi, ht0b, ht5b, p1453_1, u0elo0]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              rcases p1453_3 (m.d 0 1) (by simp) with h1458 | h1458
                              · rcases p1453_3 (m.d 0 2) (by simp) with h1459 | h1459
                                · linarith only [h0, h1459, hlam]
                                · linarith only [h1371, h1459, hlam]
                              · linarith only [h1458, h3, hlam]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [h0, hlam, p1453_0]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [hlam, p1453_0]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [h4, hlam, p1453_0]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [h1025, hlam, p1453_1]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [h1409, h4, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1453_1]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [h1, hlam, p1453_1]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [h0, h1404, hc25, hlam, hphi, ht0b, ht5b, p1453_1, u0elo2]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [hlam, p1453_0]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [h1372, hlam, p1453_1]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              rcases p1453_3 (m.d 0 1) (by simp) with h1472 | h1472
                              · rcases p1453_3 (m.d 0 2) (by simp) with h1473 | h1473
                                · linarith only [h1473, h4, hlam]
                                · linarith only [h1371, h1473, hlam]
                              · linarith only [h1472, h3, hlam]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [h2, hlam, p1453_0]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [h1371, h1450, h1452, h2, hc45, hlam, hphi, ht0b, ht5b, p1453_1, u0elo0]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [h1371, h1450, h1452, h2, h4, hc45, hlam, hphi, ht0b, ht5b, p1453_1, u0elo0]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [hlam, p1453_0]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              rcases p1453_3 (m.d 0 1) (by simp) with h1481 | h1481
                              · rcases p1453_3 (m.d 0 2) (by simp) with h1482 | h1482
                                · linarith only [h1025, h1482, hlam]
                                · linarith only [h1371, h1482, hlam]
                              · linarith only [h1481, h3, hlam]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [h3, hlam, p1453_0]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [h1371, hlam, p1453_1]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [h1398, hlam, p1453_0]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [h1399, hlam, p1453_1]
                            · have p1453_0 := h1453c.1
                              have p1453_1 := h1453c.2.1
                              have p1453_2 := h1453c.2.2.1
                              have p1453_3 := h1453c.2.2.2
                              linarith only [hlam, p1453_0]
                          · linarith only [h0, h1404, h1409, h1450, h1452, h4, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                        · linarith only [h1025, h1400, h1404, h1405, h1408, h1451, h2, h3, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                      · linarith only [h0, h1398, h1404, h1450, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                  · linarith only [h1399, h1400, h1404, h1405, h1408, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                · linarith only [h1372, h1398, h1400, h1404, h1407, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
            · linarith only [h1371, h1404, h4, hc12, hc23, hlam, hphi]
      · linarith only [h1025, h1371, h1399, hlam]
    · linarith only [h1371, h1398, h4, hlam]

end R2N4
