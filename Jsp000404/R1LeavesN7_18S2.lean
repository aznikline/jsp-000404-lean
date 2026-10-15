import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_18S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5360000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 1 2 3 (by decide) (by decide) with h897 | h897
  · rcases m.htr 1 2 4 (by decide) (by decide) with h898 | h898
    · rcases m.htr 1 2 5 (by decide) (by decide) with h899 | h899
      · rcases m.htr 1 3 4 (by decide) (by decide) with h900 | h900
        · rcases m.htr 1 3 5 (by decide) (by decide) with h901 | h901
          · rcases m.htr 2 3 4 (by decide) (by decide) with h902 | h902
            · rcases m.htr 2 3 5 (by decide) (by decide) with h903 | h903
              · rcases m.htr 2 4 5 (by decide) (by decide) with h904 | h904
                · linarith only [h2, h898, h9, h904, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h906 | h906
                  · linarith only [h1, h897, h9, h902, h906, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h0bigk with h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c | h908c
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      linarith only [hlam, p908_0]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      linarith only [h0, h897, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p908_1]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      linarith only [h4, h903, hc01, hc35, hlam, hphi, ht0b, ht5b, p908_1]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      rcases p908_3 (m.d 0 1) (by simp) with h912 | h912
                      · rcases p908_3 (m.d 0 2) (by simp) with h913 | h913
                        · linarith only [h0, h913, hlam]
                        · linarith only [h5, h913, hlam]
                      · linarith only [h2, h912, hlam]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      rcases p908_3 (m.d 0 1) (by simp) with h917 | h917
                      · rcases p908_3 (m.d 0 2) (by simp) with h918 | h918
                        · linarith only [h0, h918, hlam]
                        · linarith only [h6, h918, hlam]
                      · linarith only [h3, h917, hlam]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      linarith only [h0, hlam, p908_0]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      linarith only [hlam, p908_0]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      linarith only [h1, h897, h903, h906, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p908_1]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      rcases p908_3 (m.d 0 1) (by simp) with h925 | h925
                      · rcases p908_3 (m.d 0 2) (by simp) with h926 | h926
                        · rcases p908_3 (m.d 0 3) (by simp) with h927 | h927
                          · linarith only [h4, h927, hlam]
                          · linarith only [h7, h927, hlam]
                        · linarith only [h5, h926, hlam]
                      · linarith only [h2, h925, hlam]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      rcases p908_3 (m.d 0 1) (by simp) with h932 | h932
                      · rcases p908_3 (m.d 0 2) (by simp) with h933 | h933
                        · rcases p908_3 (m.d 0 3) (by simp) with h934 | h934
                          · linarith only [h4, h934, hlam]
                          · linarith only [h8, h934, hlam]
                        · linarith only [h6, h933, hlam]
                      · linarith only [h3, h932, hlam]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      linarith only [h1, hlam, p908_1]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      linarith only [h4, hlam, p908_1]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      linarith only [hlam, p908_0]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      rcases p908_3 (m.d 0 1) (by simp) with h942 | h942
                      · rcases p908_3 (m.d 0 2) (by simp) with h943 | h943
                        · rcases p908_3 (m.d 0 3) (by simp) with h944 | h944
                          · rcases p908_3 (m.d 0 4) (by simp) with h945 | h945
                            · linarith only [h7, h945, hlam]
                            · rcases p908_3 (m.d 0 5) (by simp) with h947 | h947
                              · linarith only [h8, h947, hlam]
                              · linarith only [h9, h947, hlam]
                          · linarith only [h7, h944, hlam]
                        · linarith only [h5, h943, hlam]
                      · linarith only [h2, h942, hlam]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      rcases p908_3 (m.d 0 1) (by simp) with h953 | h953
                      · rcases p908_3 (m.d 0 2) (by simp) with h954 | h954
                        · rcases p908_3 (m.d 0 3) (by simp) with h955 | h955
                          · rcases p908_3 (m.d 0 4) (by simp) with h956 | h956
                            · linarith only [h7, h956, hlam]
                            · rcases p908_3 (m.d 0 5) (by simp) with h958 | h958
                              · linarith only [h8, h958, hlam]
                              · rcases h2bigk with h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c | h960c
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  linarith only [hlam, p960_0]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  linarith only [h0, h897, h903, h906, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p960_1]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  rcases p960_3 (m.d 0 2) (by simp) with h963 | h963
                                  · rcases p960_3 (m.d 1 2) (by simp) with h964 | h964
                                    · linarith only [h0, h964, hlam]
                                    · linarith only [h897, h964, hlam]
                                  · linarith only [h963, hlam, p960_0]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  linarith only [h2, h4, h898, h9, hlam, p908_1, p960_2]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  linarith only [h3, h4, h899, hlam, p908_1, p960_2]
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
                                  linarith only [h0, h903, h906, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p960_1]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  rcases p960_3 (m.d 0 2) (by simp) with h973 | h973
                                  · rcases p960_3 (m.d 1 2) (by simp) with h974 | h974
                                    · rcases p960_3 (m.d 2 3) (by simp) with h975 | h975
                                      · linarith only [h897, h975, hlam]
                                      · linarith only [h902, h975, hlam]
                                    · linarith only [h974, hlam, p960_0]
                                  · linarith only [h5, h973, hlam]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  rcases p960_3 (m.d 0 2) (by simp) with h980 | h980
                                  · rcases p960_3 (m.d 1 2) (by simp) with h981 | h981
                                    · rcases p960_3 (m.d 2 3) (by simp) with h982 | h982
                                      · linarith only [h897, h982, hlam]
                                      · linarith only [h903, h982, hlam]
                                    · linarith only [h981, hlam, p960_0]
                                  · linarith only [h6, h980, hlam]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  linarith only [h4, hlam, p960_0]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  linarith only [h897, hlam, p960_0]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  linarith only [hlam, p960_0]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  linarith only [h0, h897, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p960_1]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  linarith only [h0, h897, hc01, hc25, hlam, hphi, ht0b, ht5b, p960_1]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  linarith only [h5, hlam, p960_0]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  linarith only [h898, hlam, p960_0]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  linarith only [h902, hlam, p960_1]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  linarith only [hlam, p960_0]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  linarith only [h904, hlam, p960_1]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  linarith only [h6, hlam, p960_0]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  linarith only [h899, hlam, p960_0]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  linarith only [h903, hlam, p960_1]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  linarith only [h0, h4, h6, h902, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p908_1, p960_1]
                                · have p960_0 := h960c.1
                                  have p960_1 := h960c.2.1
                                  have p960_2 := h960c.2.2.1
                                  have p960_3 := h960c.2.2.2
                                  linarith only [hlam, p960_0]
                          · linarith only [h8, h955, hlam]
                        · linarith only [h6, h954, hlam]
                      · linarith only [h3, h953, hlam]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      linarith only [h2, hlam, p908_0]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      linarith only [h5, hlam, p908_0]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      linarith only [h7, hlam, p908_0]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      linarith only [hlam, p908_0]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      linarith only [h9, hlam, p908_0]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      linarith only [h3, hlam, p908_0]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      linarith only [h6, hlam, p908_1]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      linarith only [h8, hlam, p908_0]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      linarith only [h5, h9, h902, hc34, hc45, hlam, hphi, p908_1]
                    · have p908_0 := h908c.1
                      have p908_1 := h908c.2.1
                      have p908_2 := h908c.2.2.1
                      have p908_3 := h908c.2.2.2
                      linarith only [hlam, p908_0]
              · linarith only [h0, h897, h901, h902, h903, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1016 | h1016
              · linarith only [h0, h1016, h897, h900, h902, hc01, hc35, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1018 | h1018
                · linarith only [h0, h1018, h2, h5, h9, h900, h902, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1020 | h1020
                  · linarith only [h1020, h2, h9, h900, hlam]
                  · rcases h0bigk with h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c | h1022c
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [hlam, p1022_0]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h0, h1020, h897, h901, h902, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1022_1]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h1, h1020, h901, h902, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1022_1]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h2, h900, h902, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1022_1]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h1020, h8, h902, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1022_1]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h0, hlam, p1022_0]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [hlam, p1022_0]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h1, h1020, h901, h902, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1022_1]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h0, h2, h900, h902, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1022_1]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h0, h1020, h8, h902, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1022_1]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h1, hlam, p1022_1]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h4, hlam, p1022_1]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [hlam, p1022_0]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h2, h900, h902, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1022_1]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h0, h1020, h4, h8, h902, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1022_1]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h2, hlam, p1022_0]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h5, hlam, p1022_0]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h7, hlam, p1022_0]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [hlam, p1022_0]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h9, hlam, p1022_0]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h3, hlam, p1022_0]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h6, hlam, p1022_1]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h8, hlam, p1022_0]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [h2, h900, h902, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1022_1]
                    · have p1022_0 := h1022c.1
                      have p1022_1 := h1022c.2.1
                      have p1022_2 := h1022c.2.2.1
                      have p1022_3 := h1022c.2.2.2
                      linarith only [hlam, p1022_0]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1048 | h1048
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1049 | h1049
              · linarith only [h0, h1049, h897, h901, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1051 | h1051
                · linarith only [h1048, h1051, h2, h8, h897, h898, h9, h901, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1053 | h1053
                  · linarith only [h1048, h1053, h4, h8, h897, h9, h901, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases h0bigk with h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c | h1055c
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [hlam, p1055_0]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [h4, h8, h901, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1055_1]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [h1048, h8, h897, h901, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1055_1]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      rcases p1055_3 (m.d 0 1) (by simp) with h1059 | h1059
                      · rcases p1055_3 (m.d 0 2) (by simp) with h1060 | h1060
                        · linarith only [h0, h1060, hlam]
                        · linarith only [h1060, h5, hlam]
                      · linarith only [h1059, h2, hlam]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [h1048, h8, h897, h901, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1055_1]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [h0, hlam, p1055_0]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [hlam, p1055_0]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [h1048, h8, h897, h901, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1055_1]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      rcases p1055_3 (m.d 0 1) (by simp) with h1068 | h1068
                      · rcases p1055_3 (m.d 0 2) (by simp) with h1069 | h1069
                        · rcases p1055_3 (m.d 0 3) (by simp) with h1070 | h1070
                          · linarith only [h1070, h4, hlam]
                          · linarith only [h1070, h7, hlam]
                        · linarith only [h1069, h5, hlam]
                      · linarith only [h1068, h2, hlam]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [h0, h1048, h8, h897, h901, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1055_1]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [h1, hlam, p1055_1]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [h4, hlam, p1055_1]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [hlam, p1055_0]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      rcases p1055_3 (m.d 0 1) (by simp) with h1079 | h1079
                      · rcases p1055_3 (m.d 0 2) (by simp) with h1080 | h1080
                        · rcases p1055_3 (m.d 0 3) (by simp) with h1081 | h1081
                          · rcases p1055_3 (m.d 0 4) (by simp) with h1082 | h1082
                            · linarith only [h1082, h7, hlam]
                            · rcases p1055_3 (m.d 0 5) (by simp) with h1084 | h1084
                              · linarith only [h1084, h8, hlam]
                              · linarith only [h1084, h9, hlam]
                          · linarith only [h1081, h7, hlam]
                        · linarith only [h1080, h5, hlam]
                      · linarith only [h1079, h2, hlam]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [h0, h1048, h4, h8, h897, h901, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1055_1]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [h2, hlam, p1055_0]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [h5, hlam, p1055_0]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [h7, hlam, p1055_0]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [hlam, p1055_0]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [h9, hlam, p1055_0]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [h3, hlam, p1055_0]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [h6, hlam, p1055_1]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [h8, hlam, p1055_0]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [h9, hc04, hc45, hlam, hphi, p1055_1]
                    · have p1055_0 := h1055c.1
                      have p1055_1 := h1055c.2.1
                      have p1055_2 := h1055c.2.2.1
                      have p1055_3 := h1055c.2.2.2
                      linarith only [hlam, p1055_0]
            · linarith only [h1048, h900, h901, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1102 | h1102
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1103 | h1103
            · linarith only [h0, h1102, h1103, h4, h900, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1105 | h1105
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1106 | h1106
                · linarith only [h1105, h1106, h7, h897, h9, h900, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h1103, h1105, h1106, hlam]
              · linarith only [h1102, h1105, h7, h9, h900, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1110 | h1110
            · linarith only [h0, h1110, h897, h900, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1112 | h1112
              · linarith only [h1102, h1112, h897, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1114 | h1114
                · linarith only [h1114, h5, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1116 | h1116
                  · linarith only [h1116, h7, h9, hlam]
                  · rcases h0bigk with h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c | h1118c
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [hlam, p1118_0]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h7, h897, h900, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h7, h897, h900, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h1116, h8, h897, h900, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h0, hlam, p1118_0]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [hlam, p1118_0]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h1116, h8, h897, h900, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h0, h7, h897, h900, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h0, h1116, h8, h897, h900, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h1, hlam, p1118_1]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h4, hlam, p1118_1]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [hlam, p1118_0]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h7, h897, h900, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h0, h1116, h4, h8, h897, h900, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h2, hlam, p1118_0]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h5, hlam, p1118_0]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h7, hlam, p1118_0]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [hlam, p1118_0]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h9, hlam, p1118_0]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h3, hlam, p1118_0]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h6, hlam, p1118_1]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h8, hlam, p1118_0]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [h7, h897, h900, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1118_1]
                    · have p1118_0 := h1118c.1
                      have p1118_1 := h1118c.2.1
                      have p1118_2 := h1118c.2.2.1
                      have p1118_3 := h1118c.2.2.2
                      linarith only [hlam, p1118_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1144 | h1144
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1145 | h1145
          · linarith only [h1145, h897, h899, hlam]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1147 | h1147
            · linarith only [h0, h1147, h6, h897, h899, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h1144, h1147, h6, h897, h899, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1150 | h1150
          · linarith only [h1144, h1150, h7, h897, h899, h9, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1152 | h1152
            · linarith only [h0, h1152, h6, h897, h899, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1154 | h1154
              · linarith only [h1150, h1152, h1154, h898, h899, hlam]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1156 | h1156
                · linarith only [h1156, h898, h899, h9, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1158 | h1158
                  · linarith only [h1152, h1154, h1158, h8, h898, h899, h9, hc23, hc34, hlam, hphi]
                  · rcases h0bigk with h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c | h1160c
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [hlam, p1160_0]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h1152, h1154, h4, h8, h898, h899, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1160_1]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h1152, h1154, h8, h898, h899, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1160_1]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h1144, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1160_1]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h1152, h1154, h8, h898, h899, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1160_1]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h0, hlam, p1160_0]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [hlam, p1160_0]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h1152, h1154, h8, h898, h899, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1160_1]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h0, h1144, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1160_1]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h0, h1152, h1154, h8, h898, h899, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1160_1]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h1, hlam, p1160_1]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h4, hlam, p1160_1]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [hlam, p1160_0]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h1144, h7, hc03, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1160_1]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h0, h1152, h1154, h4, h8, h898, h899, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1160_1]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h2, hlam, p1160_0]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h5, hlam, p1160_0]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h7, hlam, p1160_0]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [hlam, p1160_0]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h9, hlam, p1160_0]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h3, hlam, p1160_0]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h6, hlam, p1160_1]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h8, hlam, p1160_0]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [h1144, h7, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1160_1]
                    · have p1160_0 := h1160c.1
                      have p1160_1 := h1160c.2.1
                      have p1160_2 := h1160c.2.2.1
                      have p1160_3 := h1160c.2.2.2
                      linarith only [hlam, p1160_0]
    · linarith only [h5, h897, h898, h9, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1187 | h1187
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1188 | h1188
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1189 | h1189
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1190 | h1190
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1191 | h1191
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1192 | h1192
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1193 | h1193
                · linarith only [h1187, h1193, h897, h9, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1195 | h1195
                  · linarith only [h1187, h1191, h1195, h2, h9, hlam]
                  · rcases h0bigk with h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c | h1197c
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      linarith only [hlam, p1197_0]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      linarith only [h4, h897, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1197_1]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      linarith only [h1, h1188, h1191, h1193, h897, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1197_1]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      rcases p1197_3 (m.d 0 1) (by simp) with h1201 | h1201
                      · rcases p1197_3 (m.d 0 2) (by simp) with h1202 | h1202
                        · linarith only [h0, h1202, hlam]
                        · linarith only [h1202, h5, hlam]
                      · linarith only [h1201, h2, hlam]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      rcases p1197_3 (m.d 0 1) (by simp) with h1206 | h1206
                      · rcases p1197_3 (m.d 0 2) (by simp) with h1207 | h1207
                        · linarith only [h0, h1207, hlam]
                        · linarith only [h1207, h6, hlam]
                      · linarith only [h1206, h3, hlam]
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
                      linarith only [h1188, h1191, h1193, h4, h897, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1197_1]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      rcases p1197_3 (m.d 0 1) (by simp) with h1214 | h1214
                      · rcases p1197_3 (m.d 0 2) (by simp) with h1215 | h1215
                        · rcases p1197_3 (m.d 0 3) (by simp) with h1216 | h1216
                          · linarith only [h1216, h4, hlam]
                          · linarith only [h1216, h7, hlam]
                        · linarith only [h1215, h5, hlam]
                      · linarith only [h1214, h2, hlam]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      rcases p1197_3 (m.d 0 1) (by simp) with h1221 | h1221
                      · rcases p1197_3 (m.d 0 2) (by simp) with h1222 | h1222
                        · rcases p1197_3 (m.d 0 3) (by simp) with h1223 | h1223
                          · linarith only [h1223, h4, hlam]
                          · linarith only [h1223, h8, hlam]
                        · linarith only [h1222, h6, hlam]
                      · linarith only [h1221, h3, hlam]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      linarith only [h1, hlam, p1197_1]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      linarith only [h4, hlam, p1197_1]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      linarith only [hlam, p1197_0]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      rcases p1197_3 (m.d 0 1) (by simp) with h1231 | h1231
                      · rcases p1197_3 (m.d 0 2) (by simp) with h1232 | h1232
                        · rcases p1197_3 (m.d 0 3) (by simp) with h1233 | h1233
                          · rcases p1197_3 (m.d 0 4) (by simp) with h1234 | h1234
                            · linarith only [h1234, h7, hlam]
                            · rcases p1197_3 (m.d 0 5) (by simp) with h1236 | h1236
                              · linarith only [h1236, h8, hlam]
                              · linarith only [h1236, h9, hlam]
                          · linarith only [h1233, h7, hlam]
                        · linarith only [h1232, h5, hlam]
                      · linarith only [h1231, h2, hlam]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      rcases p1197_3 (m.d 0 1) (by simp) with h1242 | h1242
                      · rcases p1197_3 (m.d 0 2) (by simp) with h1243 | h1243
                        · rcases p1197_3 (m.d 0 3) (by simp) with h1244 | h1244
                          · rcases p1197_3 (m.d 0 4) (by simp) with h1245 | h1245
                            · linarith only [h1245, h7, hlam]
                            · rcases p1197_3 (m.d 0 5) (by simp) with h1247 | h1247
                              · linarith only [h1247, h8, hlam]
                              · rcases h2bigk with h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c | h1249c
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [hlam, p1249_0]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  rcases p1249_3 (m.d 0 2) (by simp) with h1251 | h1251
                                  · rcases p1249_3 (m.d 1 2) (by simp) with h1252 | h1252
                                    · linarith only [h0, h1252, hlam]
                                    · rcases p1249_3 (m.d 2 3) (by simp) with h1254 | h1254
                                      · linarith only [h1254, h4, hlam]
                                      · linarith only [h1254, h897, hlam]
                                  · linarith only [h0, h1251, hlam]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [h0, h1188, h1191, h1193, h897, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1249_1]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [h1188, h1193, h4, h897, hlam, p1249_2]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [h1188, h4, h897, hlam, p1249_2]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [h0, hlam, p1249_0]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [hlam, p1249_0]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [h897, hlam, p1249_0]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [h1191, h4, h897, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1249_1]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [h0, h1191, h1193, h4, h897, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1249_1]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [h4, hlam, p1249_0]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [h0, h1187, h1191, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1249_1]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [hlam, p1249_0]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  rcases p1249_3 (m.d 0 2) (by simp) with h1269 | h1269
                                  · rcases p1249_3 (m.d 1 2) (by simp) with h1270 | h1270
                                    · linarith only [h1270, h897, hlam]
                                    · linarith only [h1187, h1270, hlam]
                                  · linarith only [h1269, h5, hlam]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  rcases p1249_3 (m.d 0 2) (by simp) with h1274 | h1274
                                  · rcases p1249_3 (m.d 1 2) (by simp) with h1275 | h1275
                                    · linarith only [h1275, h897, hlam]
                                    · linarith only [h1188, h1275, hlam]
                                  · linarith only [h1274, h6, hlam]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [h5, hlam, p1249_0]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [h1187, hlam, p1249_0]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [h1191, hlam, p1249_1]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [hlam, p1249_0]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [h1193, hlam, p1249_1]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [h6, hlam, p1249_0]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [h1188, hlam, p1249_0]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [h1192, hlam, p1249_1]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [h0, h1188, h1191, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1249_1]
                                · have p1249_0 := h1249c.1
                                  have p1249_1 := h1249c.2.1
                                  have p1249_2 := h1249c.2.2.1
                                  have p1249_3 := h1249c.2.2.2
                                  linarith only [hlam, p1249_0]
                          · linarith only [h1244, h8, hlam]
                        · linarith only [h1243, h6, hlam]
                      · linarith only [h1242, h3, hlam]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      linarith only [h2, hlam, p1197_0]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      linarith only [h5, hlam, p1197_0]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      linarith only [h7, hlam, p1197_0]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      linarith only [hlam, p1197_0]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      linarith only [h9, hlam, p1197_0]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      linarith only [h3, hlam, p1197_0]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      linarith only [h6, hlam, p1197_1]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      linarith only [h8, hlam, p1197_0]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      linarith only [h1187, h1191, h2, h9, hc34, hc45, hlam, hphi, p1197_1]
                    · have p1197_0 := h1197c.1
                      have p1197_1 := h1197c.2.1
                      have p1197_2 := h1197c.2.2.1
                      have p1197_3 := h1197c.2.2.2
                      linarith only [hlam, p1197_0]
              · linarith only [h0, h1188, h1192, h4, h8, h897, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h1188, h1191, h4, h7, h897, hc01, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h1188, h1190, h897, hlam]
        · linarith only [h1187, h1189, h7, h897, h9, hc24, hc45, hlam, hphi]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1306 | h1306
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1307 | h1307
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1308 | h1308
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1309 | h1309
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1310 | h1310
                · linarith only [h1187, h1188, h1309, h1310, h9, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1312 | h1312
                  · linarith only [h1187, h1188, h1308, h1312, h6, h9, hlam]
                  · rcases h0bigk with h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c | h1314c
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [hlam, p1314_0]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [h1188, h1309, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1314_1]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [h1, h1187, h1188, h1307, h1308, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1314_1]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      rcases p1314_3 (m.d 0 1) (by simp) with h1318 | h1318
                      · rcases p1314_3 (m.d 0 2) (by simp) with h1319 | h1319
                        · linarith only [h0, h1319, hlam]
                        · linarith only [h1319, h5, hlam]
                      · linarith only [h1318, h2, hlam]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [h1187, h1188, h1308, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1314_1]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [h0, hlam, p1314_0]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [hlam, p1314_0]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [h1187, h1188, h1308, h1309, h4, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1314_1]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      rcases p1314_3 (m.d 0 1) (by simp) with h1327 | h1327
                      · rcases p1314_3 (m.d 0 2) (by simp) with h1328 | h1328
                        · rcases p1314_3 (m.d 0 3) (by simp) with h1329 | h1329
                          · linarith only [h1329, h4, hlam]
                          · linarith only [h1329, h7, hlam]
                        · linarith only [h1328, h5, hlam]
                      · linarith only [h1327, h2, hlam]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [h0, h1187, h1188, h1308, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1314_1]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [h1, hlam, p1314_1]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [h4, hlam, p1314_1]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [hlam, p1314_0]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      rcases p1314_3 (m.d 0 1) (by simp) with h1338 | h1338
                      · rcases p1314_3 (m.d 0 2) (by simp) with h1339 | h1339
                        · rcases p1314_3 (m.d 0 3) (by simp) with h1340 | h1340
                          · rcases p1314_3 (m.d 0 4) (by simp) with h1341 | h1341
                            · linarith only [h1341, h7, hlam]
                            · rcases p1314_3 (m.d 0 5) (by simp) with h1343 | h1343
                              · linarith only [h1343, h8, hlam]
                              · linarith only [h1343, h9, hlam]
                          · linarith only [h1340, h7, hlam]
                        · linarith only [h1339, h5, hlam]
                      · linarith only [h1338, h2, hlam]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [h1187, h1188, h1308, h6, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1314_1]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [h2, hlam, p1314_0]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [h5, hlam, p1314_0]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [h7, hlam, p1314_0]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [hlam, p1314_0]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [h9, hlam, p1314_0]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [h3, hlam, p1314_0]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [h6, hlam, p1314_1]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [h8, hlam, p1314_0]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [h1187, h1308, h2, h9, hc34, hc45, hlam, hphi, p1314_1]
                    · have p1314_0 := h1314c.1
                      have p1314_1 := h1314c.2.1
                      have p1314_2 := h1314c.2.2.1
                      have p1314_3 := h1314c.2.2.2
                      linarith only [hlam, p1314_0]
              · linarith only [h1187, h1307, h1308, h1309, h897, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h0, h1187, h1308, h4, h7, h897, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1362 | h1362
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1363 | h1363
              · linarith only [h0, h1187, h1307, h1362, h1363, h4, h897, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1187, h1362, h1363, h4, h8, h897, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h0, h1187, h1362, h4, h7, h897, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h1187, h1306, h7, h897, h9, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1368 | h1368
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1369 | h1369
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1370 | h1370
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1371 | h1371
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1372 | h1372
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1373 | h1373
                · linarith only [h1373, h5, h9, hlam]
                · linarith only [h1187, h1368, h1373, hlam]
              · linarith only [h0, h1187, h1368, h1371, h1372, h4, h8, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h1368, h1371, h7, h897, h9, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
          · linarith only [h1368, h1370, h897, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1379 | h1379
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1380 | h1380
            · linarith only [h0, h1368, h1369, h1380, h4, h897, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h1368, h1380, h7, h897, h9, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
          · linarith only [h1368, h1379, h897, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1384 | h1384
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1385 | h1385
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1386 | h1386
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1387 | h1387
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1388 | h1388
                · linarith only [h1388, h5, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1390 | h1390
                  · linarith only [h1187, h1384, h1390, h5, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases h0bigk with h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c | h1392c
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [hlam, p1392_0]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h4, h897, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1392_1]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h1, h1385, hc01, hc35, hlam, hphi, ht0b, ht5b, p1392_1]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h1187, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1392_1]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h1187, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1392_1]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h0, hlam, p1392_0]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [hlam, p1392_0]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h1187, h5, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1392_1]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h0, h1187, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1392_1]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h0, h1187, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1392_1]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h1, hlam, p1392_1]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h4, hlam, p1392_1]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [hlam, p1392_0]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h1187, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1392_1]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h0, h1187, h4, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1392_1]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h2, hlam, p1392_0]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h5, hlam, p1392_0]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h7, hlam, p1392_0]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [hlam, p1392_0]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h9, hlam, p1392_0]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h3, hlam, p1392_0]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h6, hlam, p1392_1]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h8, hlam, p1392_0]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [h1187, h5, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1392_1]
                    · have p1392_0 := h1392c.1
                      have p1392_1 := h1392c.2.1
                      have p1392_2 := h1392c.2.2.1
                      have p1392_3 := h1392c.2.2.2
                      linarith only [hlam, p1392_0]
              · linarith only [h1, h1187, h1385, h1386, h1387, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h1386, h7, h897, h9, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1420 | h1420
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1421 | h1421
              · linarith only [h0, h1384, h1385, h1421, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1423 | h1423
                · linarith only [h1423, h5, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1425 | h1425
                  · linarith only [h1187, h1384, h1420, h1421, h1425, h8, h9, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases h0bigk with h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c | h1427c
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h1, h1384, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1427_1]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h1, h1384, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1427_1]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h1187, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1427_1]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h1187, h1420, h1421, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1427_1]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h0, hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h1187, h1420, h4, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1427_1]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h0, h1187, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1427_1]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h0, h1187, h1420, h1421, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1427_1]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h1, hlam, p1427_1]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h4, hlam, p1427_1]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h1187, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1427_1]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h0, h1187, h1420, h1421, h4, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1427_1]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h2, hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h5, hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h7, hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h9, hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h3, hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h6, hlam, p1427_1]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h8, hlam, p1427_0]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [h1187, h5, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1427_1]
                    · have p1427_0 := h1427c.1
                      have p1427_1 := h1427c.2.1
                      have p1427_2 := h1427c.2.2.1
                      have p1427_3 := h1427c.2.2.2
                      linarith only [hlam, p1427_0]
            · linarith only [h1, h1384, h1420, h897, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1454 | h1454
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1455 | h1455
            · linarith only [h0, h1384, h1454, h1455, h4, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · linarith only [h1455, h7, h897, h9, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 2 3 4 (by decide) (by decide) with h1458 | h1458
            · rcases m.htr 2 3 5 (by decide) (by decide) with h1459 | h1459
              · rcases m.htr 2 4 5 (by decide) (by decide) with h1460 | h1460
                · linarith only [h1460, h5, h9, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h1462 | h1462
                  · linarith only [h1458, h1462, h5, h9, hlam]
                  · rcases h0bigk with h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c | h1464c
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h1384, h1459, h1462, h4, h897, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h1384, h1459, h1462, h4, h897, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h1384, h1458, h5, h897, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h1384, h1458, h5, h897, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h0, hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h0, h1384, h1459, h1462, h4, h897, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h0, h1384, h1458, h5, h897, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h0, h1384, h1458, h5, h897, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h1, hlam, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h4, hlam, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h1384, h1458, h5, h897, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h0, h1384, h1458, h4, h5, h897, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h2, hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h5, hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h7, hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h9, hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h3, hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h6, hlam, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h8, hlam, p1464_0]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [h1384, h1458, h5, h897, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1464_1]
                    · have p1464_0 := h1464c.1
                      have p1464_1 := h1464c.2.1
                      have p1464_2 := h1464c.2.2.1
                      have p1464_3 := h1464c.2.2.2
                      linarith only [hlam, p1464_0]
              · linarith only [h0, h1384, h1458, h1459, h4, h8, h897, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · linarith only [h1458, h7, h897, h9, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5360000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9

set_option maxHeartbeats 5360000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 4 5 (by decide) (by decide) with h1492 | h1492
  · linarith only [h1492, h7, h8, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1494 | h1494
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1495 | h1495
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1496 | h1496
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1497 | h1497
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1498 | h1498
            · linarith only [h1, h1498, h8, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1500 | h1500
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1501 | h1501
                · linarith only [h1, h1494, h1501, h8, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1503 | h1503
                  · linarith only [h1492, h1495, h1503, h2, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1505 | h1505
                    · linarith only [h0, h1496, h1500, h1501, h1505, hc01, hc45, hlam, hphi, ht0b, ht5b]
                    · rcases h0bigk with h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c | h1507c
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [hlam, p1507_0]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h0, h1496, h1501, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1500, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        rcases p1507_3 (m.d 0 1) (by simp) with h1511 | h1511
                        · rcases p1507_3 (m.d 0 2) (by simp) with h1512 | h1512
                          · linarith only [h0, h1512, hlam]
                          · linarith only [h1512, h5, hlam]
                        · linarith only [h1511, h2, hlam]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1, h1494, h1500, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h0, hlam, p1507_0]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [hlam, p1507_0]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1, h1494, h1500, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        rcases p1507_3 (m.d 0 1) (by simp) with h1520 | h1520
                        · rcases p1507_3 (m.d 0 2) (by simp) with h1521 | h1521
                          · rcases p1507_3 (m.d 0 3) (by simp) with h1522 | h1522
                            · linarith only [h1522, h4, hlam]
                            · linarith only [h1522, h7, hlam]
                          · linarith only [h1521, h5, hlam]
                        · linarith only [h1520, h2, hlam]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h0, h1, h1494, h1500, h8, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1, hlam, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h4, hlam, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [hlam, p1507_0]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1495, h2, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h8, hlam, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h2, hlam, p1507_0]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h5, hlam, p1507_0]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h7, hlam, p1507_0]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [hlam, p1507_0]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1492, hlam, p1507_0]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h3, hlam, p1507_0]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h6, hlam, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1500, h3, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [h1495, h1505, h2, h8, hc24, hc45, hlam, hphi, p1507_1]
                      · have p1507_0 := h1507c.1
                        have p1507_1 := h1507c.2.1
                        have p1507_2 := h1507c.2.2.1
                        have p1507_3 := h1507c.2.2.2
                        linarith only [hlam, p1507_0]
              · linarith only [h1, h1497, h1500, h8, hc23, hc35, hlam, hphi]
          · linarith only [h1497, h7, h8, hc13, hc35, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1545 | h1545
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1546 | h1546
            · linarith only [h1, h1546, h8, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1548 | h1548
              · linarith only [h0, h1494, h1496, h1548, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h1, h1545, h1548, h8, hc23, hc35, hlam, hphi]
          · linarith only [h1545, h7, h8, hc13, hc35, hlam, hphi]
      · linarith only [h1492, h1494, h1495, h5, hc23, hc45, hlam, hphi, ht34]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1553 | h1553
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1554 | h1554
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1555 | h1555
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1556 | h1556
            · linarith only [h1494, h1553, h1556, h4, h8, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h1494, h1554, h1556, hlam]
          · linarith only [h1494, h1553, h1555, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1560 | h1560
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1561 | h1561
            · linarith only [h1, h1561, h8, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1563 | h1563
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1564 | h1564
                · linarith only [h1564, h4, h8, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1566 | h1566
                  · linarith only [h1492, h1494, h1553, h1566, h4, hc03, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1568 | h1568
                    · linarith only [h1492, h1494, h1553, h1563, h1568, h4, h8, hlam]
                    · linarith only [h1494, h1553, h1568, h4, h8, hc24, hc45, hlam, hphi]
              · linarith only [h1494, h1553, h1563, h7, h8, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · linarith only [h1560, h7, h8, hc13, hc35, hlam, hphi]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1573 | h1573
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1574 | h1574
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1575 | h1575
            · linarith only [h1, h1575, h8, hlam]
            · linarith only [h1494, h1573, h1575, hlam]
          · linarith only [h1494, h1574, h7, h8, hc12, hc35, hlam, hphi, ht23]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1579 | h1579
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1580 | h1580
            · linarith only [h1, h1580, h8, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1582 | h1582
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1583 | h1583
                · linarith only [h1583, h4, h8, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1585 | h1585
                  · linarith only [h1492, h1585, h5, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1587 | h1587
                    · linarith only [h1492, h1553, h1587, h5, hc12, hc34, hlam, hphi, ht23]
                    · rcases h0bigk with h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c | h1589c
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1494, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1553, h5, h7, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1553, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1553, h5, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h0, hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1553, h5, h7, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h0, h1553, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h0, h1553, h5, h7, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1, hlam, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h4, hlam, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1553, h5, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h8, hlam, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h2, hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h5, hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h7, hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1492, hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h3, hlam, p1589_0]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h6, hlam, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1, h1579, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [h1553, h5, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1589_1]
                      · have p1589_0 := h1589c.1
                        have p1589_1 := h1589c.2.1
                        have p1589_2 := h1589c.2.2.1
                        have p1589_3 := h1589c.2.2.2
                        linarith only [hlam, p1589_0]
              · linarith only [h1494, h1573, h1579, h1580, h1582, hc12, hc25, hlam, hphi]
          · linarith only [h1579, h7, h8, hc13, hc35, hlam, hphi]

set_option maxHeartbeats 5360000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s6_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8

end R2N4
