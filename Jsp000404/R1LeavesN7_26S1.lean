import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5008000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h883 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 2 5 (by decide) (by decide) with h884 | h884
  · rcases m.htr 0 3 4 (by decide) (by decide) with h885 | h885
    · rcases m.htr 0 3 5 (by decide) (by decide) with h886 | h886
      · rcases m.htr 0 4 5 (by decide) (by decide) with h887 | h887
        · rcases m.htr 1 2 3 (by decide) (by decide) with h888 | h888
          · linarith only [h0, h4, h883, h888, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h890 | h890
            · rcases m.htr 1 2 5 (by decide) (by decide) with h891 | h891
              · rcases m.htr 1 3 4 (by decide) (by decide) with h892 | h892
                · rcases m.htr 1 3 5 (by decide) (by decide) with h893 | h893
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h894 | h894
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h895 | h895
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h896 | h896
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h897 | h897
                          · rcases h0bigk with h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c | h898c
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [hlam, p898_0]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [h0, h890, h895, h896, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p898_1, u3ehi4]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [h0, h4, h890, h895, h896, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p898_1, u3ehi4]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              rcases p898_3 (m.d 0 1) (by simp) with h902 | h902
                              · rcases p898_3 (m.d 0 2) (by simp) with h903 | h903
                                · linarith only [h0, h903, hlam]
                                · linarith only [h883, h903, hlam]
                              · linarith only [h2, h902, hlam]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              rcases p898_3 (m.d 0 1) (by simp) with h907 | h907
                              · rcases p898_3 (m.d 0 2) (by simp) with h908 | h908
                                · linarith only [h0, h908, hlam]
                                · linarith only [h884, h908, hlam]
                              · linarith only [h3, h907, hlam]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [h0, hlam, p898_0]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [hlam, p898_0]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [h4, hlam, p898_0]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [h3, h4, h887, h891, h895, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p898_1, u3ehi4]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [h3, h4, h891, h895, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p898_1, u3ehi4]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [h1, hlam, p898_1]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [h0, h890, h895, h896, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p898_1, u3ehi4]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [hlam, p898_0]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              rcases p898_3 (m.d 0 1) (by simp) with h920 | h920
                              · rcases p898_3 (m.d 0 2) (by simp) with h921 | h921
                                · linarith only [h4, h921, hlam]
                                · linarith only [h883, h921, hlam]
                              · linarith only [h2, h920, hlam]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              rcases p898_3 (m.d 0 1) (by simp) with h925 | h925
                              · rcases p898_3 (m.d 0 2) (by simp) with h926 | h926
                                · linarith only [h4, h926, hlam]
                                · linarith only [h884, h926, hlam]
                              · linarith only [h3, h925, hlam]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [h2, hlam, p898_0]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [h883, hlam, p898_0]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [h885, hlam, p898_0]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [hlam, p898_0]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [h3, h4, h883, h891, h895, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p898_1, u3ehi4]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [h3, hlam, p898_0]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [h884, hlam, p898_1]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [h886, hlam, p898_0]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [h887, hlam, p898_1]
                            · have p898_0 := h898c.1
                              have p898_1 := h898c.2.1
                              have p898_2 := h898c.2.2.1
                              have p898_3 := h898c.2.2.2
                              linarith only [hlam, p898_0]
                          · linarith only [h4, h883, h887, h897, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h4, h883, h887, h894, h896, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h4, h883, h894, h895, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h1, h3, h4, h883, h887, h892, h893, h894, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h892, h893, hc35, hlam, hphi, u3ehi3]
                · linarith only [h888, h890, h892, hlam]
              · linarith only [h4, h884, h891, hc12, hc23, hlam, hphi]
            · linarith only [h4, h883, h890, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h948 | h948
          · linarith only [h0, h4, h883, h948, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h950 | h950
            · rcases m.htr 1 2 5 (by decide) (by decide) with h951 | h951
              · rcases m.htr 1 3 4 (by decide) (by decide) with h952 | h952
                · rcases m.htr 1 3 5 (by decide) (by decide) with h953 | h953
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h954 | h954
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h955 | h955
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h956 | h956
                        · linarith only [h2, h887, h950, h956, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h958 | h958
                          · linarith only [h2, h887, h950, h954, h958, hlam]
                          · rcases h0bigk with h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [hlam, p960_0]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [h0, h951, h954, h956, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p960_1, u3ehi3]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [h1, h948, h951, h954, h956, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p960_1, u3ehi3]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              rcases p960_3 (m.d 0 1) (by simp) with h964 | h964
                              · rcases p960_3 (m.d 0 2) (by simp) with h965 | h965
                                · linarith only [h0, h965, hlam]
                                · linarith only [h883, h965, hlam]
                              · linarith only [h2, h964, hlam]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              rcases p960_3 (m.d 0 1) (by simp) with h969 | h969
                              · rcases p960_3 (m.d 0 2) (by simp) with h970 | h970
                                · linarith only [h0, h970, hlam]
                                · linarith only [h884, h970, hlam]
                              · linarith only [h3, h969, hlam]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [h0, hlam, p960_0]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [hlam, p960_0]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [h4, hlam, p960_0]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [h2, h4, h950, h954, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p960_1, u3ehi3]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [h2, h4, h887, h950, h954, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p960_1, u3ehi3]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [h1, hlam, p960_1]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [h0, h951, h954, h956, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p960_1, u3ehi3]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [hlam, p960_0]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              rcases p960_3 (m.d 0 1) (by simp) with h982 | h982
                              · rcases p960_3 (m.d 0 2) (by simp) with h983 | h983
                                · linarith only [h4, h983, hlam]
                                · linarith only [h883, h983, hlam]
                              · linarith only [h2, h982, hlam]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              rcases p960_3 (m.d 0 1) (by simp) with h987 | h987
                              · rcases p960_3 (m.d 0 2) (by simp) with h988 | h988
                                · linarith only [h4, h988, hlam]
                                · linarith only [h884, h988, hlam]
                              · linarith only [h3, h987, hlam]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [h2, hlam, p960_0]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [h883, hlam, p960_0]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [h885, hlam, p960_0]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [hlam, p960_0]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [h887, hlam, p960_0]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [h3, hlam, p960_0]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [h884, hlam, p960_1]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [h886, hlam, p960_0]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [h2, h4, h884, h950, h954, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p960_1, u3ehi3]
                            · have p960_0 := h960c.1
                              have p960_1 := h960c.2.1
                              have p960_2 := h960c.2.2.1
                              have p960_3 := h960c.2.2.2
                              linarith only [hlam, p960_0]
                      · linarith only [h4, h883, h954, h955, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h2, h4, h884, h887, h952, h954, hlam]
                  · linarith only [h952, h953, hc35, hlam, hphi, u3ehi3]
                · linarith only [h885, h887, h952, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h4, h884, h950, h951, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h4, h883, h950, hc12, hc23, hlam, hphi]
      · linarith only [h885, h886, hc35, hlam, hphi, u3ehi3]
    · linarith only [h4, h883, h885, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1010 | h1010
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1011 | h1011
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1012 | h1012
        · linarith only [h1012, h883, h884, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1014 | h1014
          · linarith only [h0, h1014, h4, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1016 | h1016
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1017 | h1017
              · linarith only [h0, h1017, h884, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1019 | h1019
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1020 | h1020
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1021 | h1021
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1022 | h1022
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1023 | h1023
                        · linarith only [h0, h1012, h1016, h1022, h1023, h884, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1016, h1021, h1023, h884, hc45, hlam, hphi, ht34, u3ehi3]
                      · linarith only [h1, h1020, h1022, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h1, h1020, h1021, h4, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h1019, h1020, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1010, h1012, h1019, hc45, hlam, hphi, ht34, u3ehi1]
            · linarith only [h1016, h883, h884, hc12, hc25, hlam, hphi]
      · linarith only [h1010, h1011, hc35, hlam, hphi, u3ehi3]
    · linarith only [h1010, h4, h883, hlam]

set_option maxHeartbeats 5008000 in
theorem r1l7_10_12_23_L_I_L_I_M_IR_s2_x0_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_M_IR m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h883 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h1033 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h3ehi := hb3.2.1
  have h3bigk := hb3.2.2.2
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 3 4 (by decide) (by decide) with h1034 | h1034
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1035 | h1035
    · rcases m.htr 0 4 5 (by decide) (by decide) with h1036 | h1036
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1037 | h1037
        · linarith only [h0, h1037, h4, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1039 | h1039
          · linarith only [h0, h1033, h1039, h883, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1041 | h1041
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1042 | h1042
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1043 | h1043
                · rcases m.htr 2 3 4 (by decide) (by decide) with h1044 | h1044
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1045 | h1045
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1046 | h1046
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1047 | h1047
                        · rcases h0bigk with h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c | h1048c
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [hlam, p1048_0]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [h0, h1041, h1045, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1048_1, u3ehi4]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [h0, h1034, h1041, h1045, h883, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1048_1, u3ehi4]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [h0, h1041, h1045, h883, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1048_1, u3ehi4]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            rcases p1048_3 (m.d 0 1) (by simp) with h1053 | h1053
                            · rcases p1048_3 (m.d 0 2) (by simp) with h1054 | h1054
                              · linarith only [h0, h1054, hlam]
                              · linarith only [h1033, h1054, hlam]
                            · linarith only [h1053, h3, hlam]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [h0, hlam, p1048_0]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [hlam, p1048_0]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [h4, hlam, p1048_0]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [h883, hlam, p1048_1]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [h1041, h1044, h1045, h3, h883, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1048_1, u3ehi4]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [h1, hlam, p1048_1]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [h0, h1041, h1045, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1048_1, u3ehi4]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [hlam, p1048_0]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [h0, h1041, h1045, h4, h883, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1048_1, u3ehi4]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            rcases p1048_3 (m.d 0 1) (by simp) with h1067 | h1067
                            · rcases p1048_3 (m.d 0 2) (by simp) with h1068 | h1068
                              · linarith only [h1068, h4, hlam]
                              · linarith only [h1033, h1068, hlam]
                            · linarith only [h1067, h3, hlam]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [h2, hlam, p1048_0]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [h0, h1041, h1045, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1048_1, u3ehi4]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [h1034, hlam, p1048_0]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [hlam, p1048_0]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            rcases p1048_3 (m.d 0 1) (by simp) with h1076 | h1076
                            · rcases p1048_3 (m.d 0 2) (by simp) with h1077 | h1077
                              · linarith only [h1077, h883, hlam]
                              · linarith only [h1033, h1077, hlam]
                            · linarith only [h1076, h3, hlam]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [h3, hlam, p1048_0]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [h1033, hlam, p1048_1]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [h1035, hlam, p1048_0]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [h1036, hlam, p1048_1]
                          · have p1048_0 := h1048c.1
                            have p1048_1 := h1048c.2.1
                            have p1048_2 := h1048c.2.2.1
                            have p1048_3 := h1048c.2.2.2
                            linarith only [hlam, p1048_0]
                        · linarith only [h0, h1041, h1046, h1047, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1033, h1036, h1046, h883, hlam]
                    · linarith only [h0, h1041, h1043, h1044, h1045, h883, hlam]
                  · linarith only [h0, h1041, h1043, h1044, h4, hc34, hlam, hphi, u3ehi4]
                · linarith only [h1042, h1043, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1091 | h1091
                · linarith only [h1034, h1042, h1091, h4, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h1037, h1041, h1091, hlam]
            · linarith only [h1033, h1041, h883, hc12, hc24, hlam, hphi]
      · linarith only [h1033, h1036, h883, hlam]
    · linarith only [h1034, h1035, hc35, hlam, hphi, u3ehi3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1097 | h1097
    · linarith only [h1034, h1097, hc34, hlam, hphi, u3ehi4]
    · linarith only [h1033, h1097, h4, hlam]

end R2N4
