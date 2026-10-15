import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_8S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6290000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
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
  rcases m.htr 1 2 3 (by decide) (by decide) with h884 | h884
  · rcases m.htr 1 2 4 (by decide) (by decide) with h885 | h885
    · rcases m.htr 1 2 5 (by decide) (by decide) with h886 | h886
      · rcases m.htr 1 3 4 (by decide) (by decide) with h887 | h887
        · rcases m.htr 1 3 5 (by decide) (by decide) with h888 | h888
          · rcases m.htr 1 4 5 (by decide) (by decide) with h889 | h889
            · linarith only [h2, h889, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h891 | h891
              · rcases m.htr 2 3 5 (by decide) (by decide) with h892 | h892
                · linarith only [h0, h884, h892, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                · linarith only [h1, h888, h891, h892, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h895 | h895
                · linarith only [h2, h887, h891, h895, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h897 | h897
                  · linarith only [h0, h884, h887, h891, h897, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h899 | h899
                    · linarith only [h2, h887, h899, h9, hlam]
                    · rcases h0bigk with h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        linarith only [hlam, p901_0]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        linarith only [h6, hc01, hlam, hphi, ht0b, ht5b, p901_1, u5ehi2]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        linarith only [h7, h891, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p901_1]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        rcases p901_3 (m.d 0 1) (by simp) with h905 | h905
                        · rcases p901_3 (m.d 0 2) (by simp) with h906 | h906
                          · linarith only [h0, h906, hlam]
                          · linarith only [h5, h906, hlam]
                        · linarith only [h2, h905, hlam]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        rcases p901_3 (m.d 0 1) (by simp) with h910 | h910
                        · rcases p901_3 (m.d 0 2) (by simp) with h911 | h911
                          · linarith only [h0, h911, hlam]
                          · linarith only [h6, h911, hlam]
                        · linarith only [h3, h910, hlam]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        linarith only [h0, hlam, p901_0]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        linarith only [hlam, p901_0]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        linarith only [h1, h888, h891, h899, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p901_1]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        rcases p901_3 (m.d 0 1) (by simp) with h918 | h918
                        · rcases p901_3 (m.d 0 2) (by simp) with h919 | h919
                          · rcases p901_3 (m.d 0 3) (by simp) with h920 | h920
                            · linarith only [h4, h920, hlam]
                            · linarith only [h7, h920, hlam]
                          · linarith only [h5, h919, hlam]
                        · linarith only [h2, h918, hlam]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        rcases p901_3 (m.d 0 1) (by simp) with h925 | h925
                        · rcases p901_3 (m.d 0 2) (by simp) with h926 | h926
                          · rcases p901_3 (m.d 0 3) (by simp) with h927 | h927
                            · linarith only [h4, h927, hlam]
                            · linarith only [h8, h927, hlam]
                          · linarith only [h6, h926, hlam]
                        · linarith only [h3, h925, hlam]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        linarith only [h1, hlam, p901_1]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        linarith only [h4, hlam, p901_1]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        linarith only [hlam, p901_0]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        rcases p901_3 (m.d 0 1) (by simp) with h935 | h935
                        · rcases p901_3 (m.d 0 2) (by simp) with h936 | h936
                          · rcases p901_3 (m.d 0 3) (by simp) with h937 | h937
                            · rcases p901_3 (m.d 0 4) (by simp) with h938 | h938
                              · linarith only [h7, h938, hlam]
                              · rcases p901_3 (m.d 0 5) (by simp) with h940 | h940
                                · linarith only [h8, h940, hlam]
                                · linarith only [h9, h940, hlam]
                            · linarith only [h7, h937, hlam]
                          · linarith only [h5, h936, hlam]
                        · linarith only [h2, h935, hlam]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        rcases p901_3 (m.d 0 1) (by simp) with h946 | h946
                        · rcases p901_3 (m.d 0 2) (by simp) with h947 | h947
                          · rcases p901_3 (m.d 0 3) (by simp) with h948 | h948
                            · rcases p901_3 (m.d 0 4) (by simp) with h949 | h949
                              · linarith only [h7, h949, hlam]
                              · rcases p901_3 (m.d 0 5) (by simp) with h951 | h951
                                · linarith only [h8, h951, hlam]
                                · rcases h2bigk with h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c | h953c
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [hlam, p953_0]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [h0, h884, h888, h891, h899, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p953_1]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [h4, h8, h891, h899, hlam, p901_1, p953_2]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    rcases p953_3 (m.d 0 2) (by simp) with h957 | h957
                                    · rcases p953_3 (m.d 1 2) (by simp) with h958 | h958
                                      · linarith only [h0, h958, hlam]
                                      · linarith only [h885, h958, hlam]
                                    · linarith only [h957, hlam, p953_0]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    rcases p953_3 (m.d 0 2) (by simp) with h962 | h962
                                    · rcases p953_3 (m.d 1 2) (by simp) with h963 | h963
                                      · linarith only [h0, h963, hlam]
                                      · linarith only [h886, h963, hlam]
                                    · linarith only [h962, hlam, p953_0]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [h0, hlam, p953_0]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [hlam, p953_0]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    rcases p953_3 (m.d 0 2) (by simp) with h969 | h969
                                    · rcases p953_3 (m.d 1 2) (by simp) with h970 | h970
                                      · rcases p953_3 (m.d 2 3) (by simp) with h971 | h971
                                        · linarith only [h971, hlam, p953_0]
                                        · rcases p953_3 (m.d 2 4) (by simp) with h973 | h973
                                          · linarith only [h885, h973, hlam]
                                          · linarith only [h891, h973, hlam]
                                      · linarith only [h970, hlam, p953_0]
                                    · linarith only [h4, h969, hlam]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    rcases p953_3 (m.d 0 2) (by simp) with h978 | h978
                                    · rcases p953_3 (m.d 1 2) (by simp) with h979 | h979
                                      · rcases p953_3 (m.d 2 3) (by simp) with h980 | h980
                                        · linarith only [h884, h980, hlam]
                                        · rcases p953_3 (m.d 2 4) (by simp) with h982 | h982
                                          · linarith only [h982, hlam, p953_0]
                                          · rcases p953_3 (m.d 2 5) (by simp) with h984 | h984
                                            · linarith only [h886, h984, hlam]
                                            · linarith only [h897, h984, hlam]
                                      · linarith only [h979, hlam, p953_0]
                                    · linarith only [h5, h978, hlam]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p953_1, u5ehi2]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [h4, hlam, p953_0]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [h884, hlam, p953_0]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [hlam, p953_0]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [h891, hlam, p953_0]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [h895, hlam, p953_0]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [h5, hlam, p953_0]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [h885, hlam, p953_0]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [h0, h4, h5, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p901_1, p953_1]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [hlam, p953_0]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [h897, hlam, p953_1]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [h6, hlam, p953_0]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [h886, hlam, p953_0]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [h0, h4, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p901_1, p953_1]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [h0, h3, h4, h888, h895, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p901_1, p953_1]
                                  · have p953_0 := h953c.1
                                    have p953_1 := h953c.2.1
                                    have p953_2 := h953c.2.2.1
                                    have p953_3 := h953c.2.2.2
                                    linarith only [hlam, p953_0]
                            · linarith only [h8, h948, hlam]
                          · linarith only [h6, h947, hlam]
                        · linarith only [h3, h946, hlam]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        linarith only [h2, hlam, p901_0]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        linarith only [h5, hlam, p901_0]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        linarith only [h7, hlam, p901_0]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        linarith only [hlam, p901_0]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        linarith only [h9, hlam, p901_0]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        linarith only [h3, hlam, p901_0]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        linarith only [h6, hlam, p901_1]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        linarith only [h8, hlam, p901_0]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        linarith only [h2, h887, h891, h9, hc23, hc45, hlam, hphi, ht34, p901_1]
                      · have p901_0 := h901c.1
                        have p901_1 := h901c.2.1
                        have p901_2 := h901c.2.2.1
                        have p901_3 := h901c.2.2.2
                        linarith only [hlam, p901_0]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1018 | h1018
            · linarith only [h1018, h2, h8, h887, h888, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1020 | h1020
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1021 | h1021
                · linarith only [h1021, h884, h888, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1023 | h1023
                  · linarith only [h1023, h5, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1025 | h1025
                    · linarith only [h1020, h1025, h8, h884, h888, h9, hlam]
                    · rcases h0bigk with h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [hlam, p1027_0]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [h1020, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1027_1]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [h1020, h8, h884, h888, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1027_1]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        rcases p1027_3 (m.d 0 1) (by simp) with h1031 | h1031
                        · rcases p1027_3 (m.d 0 2) (by simp) with h1032 | h1032
                          · linarith only [h0, h1032, hlam]
                          · linarith only [h1032, h5, hlam]
                        · linarith only [h1031, h2, hlam]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [h1020, h8, h884, h888, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1027_1]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [h0, hlam, p1027_0]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [hlam, p1027_0]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [h1020, h8, h884, h888, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1027_1]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        rcases p1027_3 (m.d 0 1) (by simp) with h1040 | h1040
                        · rcases p1027_3 (m.d 0 2) (by simp) with h1041 | h1041
                          · rcases p1027_3 (m.d 0 3) (by simp) with h1042 | h1042
                            · linarith only [h1042, h4, hlam]
                            · linarith only [h1042, h7, hlam]
                          · linarith only [h1041, h5, hlam]
                        · linarith only [h1040, h2, hlam]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [h0, h1020, h8, h884, h888, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1027_1]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [h1, hlam, p1027_1]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [h4, hlam, p1027_1]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [hlam, p1027_0]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        rcases p1027_3 (m.d 0 1) (by simp) with h1051 | h1051
                        · rcases p1027_3 (m.d 0 2) (by simp) with h1052 | h1052
                          · rcases p1027_3 (m.d 0 3) (by simp) with h1053 | h1053
                            · rcases p1027_3 (m.d 0 4) (by simp) with h1054 | h1054
                              · linarith only [h1054, h7, hlam]
                              · rcases p1027_3 (m.d 0 5) (by simp) with h1056 | h1056
                                · linarith only [h1056, h8, hlam]
                                · linarith only [h1056, h9, hlam]
                            · linarith only [h1053, h7, hlam]
                          · linarith only [h1052, h5, hlam]
                        · linarith only [h1051, h2, hlam]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [h1020, h8, h884, h888, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1027_1]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [h2, hlam, p1027_0]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [h5, hlam, p1027_0]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [h7, hlam, p1027_0]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [hlam, p1027_0]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [h9, hlam, p1027_0]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [h3, hlam, p1027_0]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [h6, hlam, p1027_1]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [h8, hlam, p1027_0]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        rcases p1027_3 (m.d 0 1) (by simp) with h1071 | h1071
                        · rcases p1027_3 (m.d 0 2) (by simp) with h1072 | h1072
                          · rcases p1027_3 (m.d 0 3) (by simp) with h1073 | h1073
                            · rcases p1027_3 (m.d 0 4) (by simp) with h1074 | h1074
                              · linarith only [h1074, h9, hlam]
                              · rcases p1027_3 (m.d 0 5) (by simp) with h1076 | h1076
                                · rcases h2bigk with h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c | h1077c
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [hlam, p1077_0]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [h0, h1020, h884, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1077_1]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    rcases p1077_3 (m.d 0 2) (by simp) with h1080 | h1080
                                    · rcases p1077_3 (m.d 1 2) (by simp) with h1081 | h1081
                                      · linarith only [h0, h1081, hlam]
                                      · linarith only [h1081, h884, hlam]
                                    · linarith only [h1080, hlam, p1077_0]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    rcases p1077_3 (m.d 0 2) (by simp) with h1085 | h1085
                                    · rcases p1077_3 (m.d 1 2) (by simp) with h1086 | h1086
                                      · linarith only [h0, h1086, hlam]
                                      · linarith only [h1086, h885, hlam]
                                    · linarith only [h1085, hlam, p1077_0]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    rcases p1077_3 (m.d 0 2) (by simp) with h1090 | h1090
                                    · rcases p1077_3 (m.d 1 2) (by simp) with h1091 | h1091
                                      · linarith only [h0, h1091, hlam]
                                      · linarith only [h1091, h886, hlam]
                                    · linarith only [h1090, hlam, p1077_0]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [h0, hlam, p1077_0]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [hlam, p1077_0]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [h0, h1020, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1077_1]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    rcases p1077_3 (m.d 0 2) (by simp) with h1098 | h1098
                                    · rcases p1077_3 (m.d 1 2) (by simp) with h1099 | h1099
                                      · rcases p1077_3 (m.d 2 3) (by simp) with h1100 | h1100
                                        · linarith only [h1100, h884, hlam]
                                        · linarith only [h1020, h1100, hlam]
                                      · linarith only [h1099, hlam, p1077_0]
                                    · linarith only [h1098, h5, hlam]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [h0, h1020, h1021, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1077_1]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [h4, hlam, p1077_0]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [h884, hlam, p1077_0]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [hlam, p1077_0]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [h4, h8, h884, h888, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b, p1077_1]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [h1021, hlam, p1077_0]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [h5, hlam, p1077_0]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [h885, hlam, p1077_0]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [h1020, hlam, p1077_1]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [hlam, p1077_0]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [h1023, hlam, p1077_1]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [h6, hlam, p1077_0]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [h886, hlam, p1077_0]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [h0, h886, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1077_1]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [h0, h1020, h886, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1077_1]
                                  · have p1077_0 := h1077c.1
                                    have p1077_1 := h1077c.2.1
                                    have p1077_2 := h1077c.2.2.1
                                    have p1077_3 := h1077c.2.2.2
                                    linarith only [hlam, p1077_0]
                                · linarith only [h1076, h9, hlam]
                            · linarith only [h1073, h7, hlam]
                          · linarith only [h1072, h5, hlam]
                        · linarith only [h1071, h2, hlam]
                      · have p1027_0 := h1027c.1
                        have p1027_1 := h1027c.2.1
                        have p1027_2 := h1027c.2.2.1
                        have p1027_3 := h1027c.2.2.2
                        linarith only [hlam, p1027_0]
              · linarith only [h0, h1020, h4, h8, h887, h888, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1127 | h1127
          · linarith only [h1127, h7, h887, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1129 | h1129
            · linarith only [h1129, h2, h7, h887, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1131 | h1131
              · linarith only [h1131, h884, h887, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1133 | h1133
                · linarith only [h1127, h1133, h7, h884, h886, h887, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1135 | h1135
                  · linarith only [h0, h1135, h5, h7, h884, h887, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1137 | h1137
                    · linarith only [h1137, h7, h9, hlam]
                    · rcases h0bigk with h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c | h1139c
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        linarith only [hlam, p1139_0]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        linarith only [h6, hc01, hlam, hphi, ht0b, ht5b, p1139_1, u5ehi2]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        linarith only [h7, h884, h887, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1139_1]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        rcases p1139_3 (m.d 0 1) (by simp) with h1143 | h1143
                        · rcases p1139_3 (m.d 0 2) (by simp) with h1144 | h1144
                          · linarith only [h0, h1144, hlam]
                          · linarith only [h1144, h5, hlam]
                        · linarith only [h1143, h2, hlam]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        rcases p1139_3 (m.d 0 1) (by simp) with h1148 | h1148
                        · rcases p1139_3 (m.d 0 2) (by simp) with h1149 | h1149
                          · linarith only [h0, h1149, hlam]
                          · linarith only [h1149, h6, hlam]
                        · linarith only [h1148, h3, hlam]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        linarith only [h0, hlam, p1139_0]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        linarith only [hlam, p1139_0]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        linarith only [h1137, h8, h884, h887, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1139_1]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        rcases p1139_3 (m.d 0 1) (by simp) with h1156 | h1156
                        · rcases p1139_3 (m.d 0 2) (by simp) with h1157 | h1157
                          · rcases p1139_3 (m.d 0 3) (by simp) with h1158 | h1158
                            · linarith only [h1158, h4, hlam]
                            · linarith only [h1158, h7, hlam]
                          · linarith only [h1157, h5, hlam]
                        · linarith only [h1156, h2, hlam]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        rcases p1139_3 (m.d 0 1) (by simp) with h1163 | h1163
                        · rcases p1139_3 (m.d 0 2) (by simp) with h1164 | h1164
                          · rcases p1139_3 (m.d 0 3) (by simp) with h1165 | h1165
                            · linarith only [h1165, h4, hlam]
                            · linarith only [h1165, h8, hlam]
                          · linarith only [h1164, h6, hlam]
                        · linarith only [h1163, h3, hlam]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        linarith only [h1, hlam, p1139_1]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        linarith only [h4, hlam, p1139_1]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        linarith only [hlam, p1139_0]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        rcases p1139_3 (m.d 0 1) (by simp) with h1173 | h1173
                        · rcases p1139_3 (m.d 0 2) (by simp) with h1174 | h1174
                          · rcases p1139_3 (m.d 0 3) (by simp) with h1175 | h1175
                            · rcases p1139_3 (m.d 0 4) (by simp) with h1176 | h1176
                              · linarith only [h1176, h7, hlam]
                              · rcases p1139_3 (m.d 0 5) (by simp) with h1178 | h1178
                                · linarith only [h1178, h8, hlam]
                                · linarith only [h1178, h9, hlam]
                            · linarith only [h1175, h7, hlam]
                          · linarith only [h1174, h5, hlam]
                        · linarith only [h1173, h2, hlam]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        rcases p1139_3 (m.d 0 1) (by simp) with h1184 | h1184
                        · rcases p1139_3 (m.d 0 2) (by simp) with h1185 | h1185
                          · rcases p1139_3 (m.d 0 3) (by simp) with h1186 | h1186
                            · rcases p1139_3 (m.d 0 4) (by simp) with h1187 | h1187
                              · linarith only [h1187, h7, hlam]
                              · rcases p1139_3 (m.d 0 5) (by simp) with h1189 | h1189
                                · linarith only [h1189, h8, hlam]
                                · rcases h2bigk with h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c | h1191c
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [hlam, p1191_0]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [h0, h886, hc01, hlam, hphi, ht0b, ht5b, p1191_1, u5ehi2]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [h4, h7, h884, h887, h9, hlam, p1139_1, p1191_2]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    rcases p1191_3 (m.d 0 2) (by simp) with h1195 | h1195
                                    · rcases p1191_3 (m.d 1 2) (by simp) with h1196 | h1196
                                      · linarith only [h0, h1196, hlam]
                                      · linarith only [h1196, h885, hlam]
                                    · linarith only [h1195, hlam, p1191_0]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    rcases p1191_3 (m.d 0 2) (by simp) with h1200 | h1200
                                    · rcases p1191_3 (m.d 1 2) (by simp) with h1201 | h1201
                                      · linarith only [h0, h1201, hlam]
                                      · linarith only [h1201, h886, hlam]
                                    · linarith only [h1200, hlam, p1191_0]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [h0, hlam, p1191_0]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [hlam, p1191_0]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    rcases p1191_3 (m.d 0 2) (by simp) with h1207 | h1207
                                    · rcases p1191_3 (m.d 1 2) (by simp) with h1208 | h1208
                                      · rcases p1191_3 (m.d 2 3) (by simp) with h1209 | h1209
                                        · linarith only [h1209, hlam, p1191_0]
                                        · rcases p1191_3 (m.d 2 4) (by simp) with h1211 | h1211
                                          · linarith only [h1211, h885, hlam]
                                          · linarith only [h1131, h1211, hlam]
                                      · linarith only [h1208, hlam, p1191_0]
                                    · linarith only [h1207, h4, hlam]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    rcases p1191_3 (m.d 0 2) (by simp) with h1216 | h1216
                                    · rcases p1191_3 (m.d 1 2) (by simp) with h1217 | h1217
                                      · rcases p1191_3 (m.d 2 3) (by simp) with h1218 | h1218
                                        · linarith only [h1218, h884, hlam]
                                        · rcases p1191_3 (m.d 2 4) (by simp) with h1220 | h1220
                                          · linarith only [h1220, hlam, p1191_0]
                                          · rcases p1191_3 (m.d 2 5) (by simp) with h1222 | h1222
                                            · linarith only [h1222, h886, hlam]
                                            · linarith only [h1135, h1222, hlam]
                                      · linarith only [h1217, hlam, p1191_0]
                                    · linarith only [h1216, h5, hlam]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht0b, ht5b, p1191_1, u5ehi2]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [h4, hlam, p1191_0]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [h884, hlam, p1191_0]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [hlam, p1191_0]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [h1131, hlam, p1191_0]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [h1133, hlam, p1191_0]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [h5, hlam, p1191_0]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [h885, hlam, p1191_0]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [h4, h5, h9, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1139_1, p1191_1]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [hlam, p1191_0]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [h1135, hlam, p1191_1]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [h6, hlam, p1191_0]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [h886, hlam, p1191_0]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [h0, h3, h4, h886, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1139_1, p1191_1]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [h0, h1127, h4, h8, h886, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1139_1, p1191_1]
                                  · have p1191_0 := h1191c.1
                                    have p1191_1 := h1191c.2.1
                                    have p1191_2 := h1191c.2.2.1
                                    have p1191_3 := h1191c.2.2.2
                                    linarith only [hlam, p1191_0]
                            · linarith only [h1186, h8, hlam]
                          · linarith only [h1185, h6, hlam]
                        · linarith only [h1184, h3, hlam]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        linarith only [h2, hlam, p1139_0]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        linarith only [h5, hlam, p1139_0]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        linarith only [h7, hlam, p1139_0]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        linarith only [hlam, p1139_0]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        linarith only [h9, hlam, p1139_0]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        linarith only [h3, hlam, p1139_0]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        linarith only [h6, hlam, p1139_1]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        linarith only [h8, hlam, p1139_0]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        linarith only [h7, h884, h887, h9, hc23, hc45, hlam, hphi, ht34, p1139_1]
                      · have p1139_0 := h1139c.1
                        have p1139_1 := h1139c.2.1
                        have p1139_2 := h1139c.2.2.1
                        have p1139_3 := h1139c.2.2.2
                        linarith only [hlam, p1139_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1256 | h1256
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1257 | h1257
          · linarith only [h0, h1257, h6, h884, h886, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1259 | h1259
            · linarith only [h1259, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1261 | h1261
              · linarith only [h0, h1261, h6, h884, h886, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1256, h1261, h6, h884, h886, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1264 | h1264
          · linarith only [h1256, h1264, h7, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1266 | h1266
            · linarith only [h1266, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1268 | h1268
              · linarith only [h1256, h1268, h884, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1270 | h1270
                · linarith only [h1264, h1268, h1270, h6, h885, h886, hc02, hlam, hphi, ht0b, ht5b, u5ehi1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1272 | h1272
                  · linarith only [h0, h1270, h1272, h4, h8, h885, h886, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1274 | h1274
                    · linarith only [h1268, h1270, h1274, h8, h885, h886, h9, hc23, hc34, hlam, hphi]
                    · rcases h0bigk with h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c | h1276c
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [hlam, p1276_0]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [h1268, h1270, h4, h8, h885, h886, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1276_1]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [h1268, h1270, h8, h885, h886, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1276_1]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        rcases p1276_3 (m.d 0 1) (by simp) with h1280 | h1280
                        · rcases p1276_3 (m.d 0 2) (by simp) with h1281 | h1281
                          · linarith only [h0, h1281, hlam]
                          · linarith only [h1281, h5, hlam]
                        · linarith only [h1280, h2, hlam]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [h1268, h1270, h8, h885, h886, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1276_1]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [h0, hlam, p1276_0]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [hlam, p1276_0]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [h1268, h1270, h8, h885, h886, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1276_1]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        rcases p1276_3 (m.d 0 1) (by simp) with h1289 | h1289
                        · rcases p1276_3 (m.d 0 2) (by simp) with h1290 | h1290
                          · rcases p1276_3 (m.d 0 3) (by simp) with h1291 | h1291
                            · linarith only [h1291, h4, hlam]
                            · linarith only [h1291, h7, hlam]
                          · linarith only [h1290, h5, hlam]
                        · linarith only [h1289, h2, hlam]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [h0, h1268, h1270, h8, h885, h886, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1276_1]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [h1, hlam, p1276_1]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [h4, hlam, p1276_1]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [hlam, p1276_0]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        rcases p1276_3 (m.d 0 1) (by simp) with h1300 | h1300
                        · rcases p1276_3 (m.d 0 2) (by simp) with h1301 | h1301
                          · rcases p1276_3 (m.d 0 3) (by simp) with h1302 | h1302
                            · rcases p1276_3 (m.d 0 4) (by simp) with h1303 | h1303
                              · linarith only [h1303, h7, hlam]
                              · rcases p1276_3 (m.d 0 5) (by simp) with h1305 | h1305
                                · linarith only [h1305, h8, hlam]
                                · linarith only [h1305, h9, hlam]
                            · linarith only [h1302, h7, hlam]
                          · linarith only [h1301, h5, hlam]
                        · linarith only [h1300, h2, hlam]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [h0, h1268, h1270, h4, h8, h885, h886, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1276_1]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [h2, hlam, p1276_0]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [h5, hlam, p1276_0]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [h7, hlam, p1276_0]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [hlam, p1276_0]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [h9, hlam, p1276_0]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [h3, hlam, p1276_0]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [h6, hlam, p1276_1]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [h8, hlam, p1276_0]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [h1256, h7, h884, h9, hc23, hc45, hlam, hphi, ht34, p1276_1]
                      · have p1276_0 := h1276c.1
                        have p1276_1 := h1276c.2.1
                        have p1276_2 := h1276c.2.2.1
                        have p1276_3 := h1276c.2.2.2
                        linarith only [hlam, p1276_0]
    · linarith only [h5, h884, h885, h9, hc23, hc45, hlam, hphi, ht34]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1323 | h1323
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1324 | h1324
      · linarith only [h0, h1324, h4, h884, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1326 | h1326
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1327 | h1327
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1328 | h1328
            · linarith only [h0, h1323, h1328, h4, h884, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1330 | h1330
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1331 | h1331
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1332 | h1332
                  · linarith only [h1323, h1332, h2, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1334 | h1334
                    · linarith only [h1323, h1324, h1330, h1334, h6, h9, hlam]
                    · rcases h0bigk with h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c | h1336c
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [hlam, p1336_0]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [h1, h1327, h4, hc01, hlam, hphi, ht0b, ht5b, p1336_1, u5ehi3]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [h1, h1327, hc01, hlam, hphi, ht0b, ht5b, p1336_1, u5ehi3]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        rcases p1336_3 (m.d 0 1) (by simp) with h1340 | h1340
                        · rcases p1336_3 (m.d 0 2) (by simp) with h1341 | h1341
                          · linarith only [h0, h1341, hlam]
                          · linarith only [h1341, h5, hlam]
                        · linarith only [h1340, h2, hlam]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [h1323, h1324, h1330, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1336_1]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [h0, hlam, p1336_0]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [hlam, p1336_0]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [h1323, h1324, h1330, h6, h8, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1336_1]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        rcases p1336_3 (m.d 0 1) (by simp) with h1349 | h1349
                        · rcases p1336_3 (m.d 0 2) (by simp) with h1350 | h1350
                          · rcases p1336_3 (m.d 0 3) (by simp) with h1351 | h1351
                            · linarith only [h1351, h4, hlam]
                            · linarith only [h1351, h7, hlam]
                          · linarith only [h1350, h5, hlam]
                        · linarith only [h1349, h2, hlam]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [h0, h1323, h1324, h1330, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1336_1]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [h1, hlam, p1336_1]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [h4, hlam, p1336_1]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [hlam, p1336_0]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        rcases p1336_3 (m.d 0 1) (by simp) with h1360 | h1360
                        · rcases p1336_3 (m.d 0 2) (by simp) with h1361 | h1361
                          · rcases p1336_3 (m.d 0 3) (by simp) with h1362 | h1362
                            · rcases p1336_3 (m.d 0 4) (by simp) with h1363 | h1363
                              · linarith only [h1363, h7, hlam]
                              · rcases p1336_3 (m.d 0 5) (by simp) with h1365 | h1365
                                · linarith only [h1365, h8, hlam]
                                · linarith only [h1365, h9, hlam]
                            · linarith only [h1362, h7, hlam]
                          · linarith only [h1361, h5, hlam]
                        · linarith only [h1360, h2, hlam]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [h1323, h1324, h1330, h6, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1336_1]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [h2, hlam, p1336_0]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [h5, hlam, p1336_0]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [h7, hlam, p1336_0]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [hlam, p1336_0]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [h9, hlam, p1336_0]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [h3, hlam, p1336_0]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [h6, hlam, p1336_1]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [h8, hlam, p1336_0]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        rcases p1336_3 (m.d 0 1) (by simp) with h1380 | h1380
                        · rcases p1336_3 (m.d 0 2) (by simp) with h1381 | h1381
                          · rcases p1336_3 (m.d 0 3) (by simp) with h1382 | h1382
                            · rcases p1336_3 (m.d 0 4) (by simp) with h1383 | h1383
                              · linarith only [h1383, h9, hlam]
                              · rcases p1336_3 (m.d 0 5) (by simp) with h1385 | h1385
                                · rcases h2bigk with h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    rcases p1386_3 (m.d 0 2) (by simp) with h1388 | h1388
                                    · rcases p1386_3 (m.d 1 2) (by simp) with h1389 | h1389
                                      · linarith only [h0, h1389, hlam]
                                      · rcases p1386_3 (m.d 2 3) (by simp) with h1391 | h1391
                                        · linarith only [h1391, h4, hlam]
                                        · linarith only [h1391, h884, hlam]
                                    · linarith only [h0, h1388, hlam]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h0, h1323, h1324, h1330, h1331, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1386_1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h1323, h1324, h1331, h4, hlam, p1386_2]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h1323, h1324, h1330, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p1386_1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h0, hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h884, hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h0, h1324, h1330, h1331, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1386_1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h1324, hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h4, hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h0, h1323, h1330, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1386_1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    rcases p1386_3 (m.d 0 2) (by simp) with h1406 | h1406
                                    · rcases p1386_3 (m.d 1 2) (by simp) with h1407 | h1407
                                      · linarith only [h1407, h884, hlam]
                                      · linarith only [h1323, h1407, hlam]
                                    · linarith only [h1406, h5, hlam]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p1386_1, u5ehi2]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h5, hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h1323, hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h1330, hlam, p1386_1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h1332, hlam, p1386_1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h6, hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h0, h1323, h1330, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1386_1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h1331, hlam, p1386_1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    rcases p1386_3 (m.d 0 2) (by simp) with h1420 | h1420
                                    · rcases p1386_3 (m.d 1 2) (by simp) with h1421 | h1421
                                      · linarith only [h1324, h1421, hlam]
                                      · linarith only [h1323, h1421, hlam]
                                    · linarith only [h1420, h5, hlam]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [hlam, p1386_0]
                                · linarith only [h1385, h9, hlam]
                            · linarith only [h1382, h7, hlam]
                          · linarith only [h1381, h5, hlam]
                        · linarith only [h1380, h2, hlam]
                      · have p1336_0 := h1336c.1
                        have p1336_1 := h1336c.2.1
                        have p1336_2 := h1336c.2.2.1
                        have p1336_3 := h1336c.2.2.2
                        linarith only [hlam, p1336_0]
                · linarith only [h1323, h1327, h1330, h1331, h884, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
              · linarith only [h1330, h7, h884, h9, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1433 | h1433
            · linarith only [h1433, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1435 | h1435
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1436 | h1436
                · linarith only [h0, h1323, h1327, h1435, h1436, h4, h884, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h1323, h1435, h1436, h8, h884, h9, hc34, hc45, hlam, hphi]
              · linarith only [h0, h1323, h1435, h4, h7, h884, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h1323, h1326, h7, h884, h9, hc24, hc45, hlam, hphi]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1441 | h1441
      · linarith only [h1323, h1441, h5, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi2]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1443 | h1443
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1444 | h1444
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1445 | h1445
            · linarith only [h1323, h1445, h2, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1447 | h1447
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1448 | h1448
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1449 | h1449
                  · linarith only [h1449, h5, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1451 | h1451
                    · linarith only [h1323, h1451, h5, h9, hc12, hc34, hlam, hphi, ht23]
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
                        linarith only [h1444, h4, h884, hc01, hlam, hphi, ht0b, ht5b, p1453_1, u5ehi3]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        linarith only [h1, h1444, hc01, hlam, hphi, ht0b, ht5b, p1453_1, u5ehi3]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        rcases p1453_3 (m.d 0 1) (by simp) with h1457 | h1457
                        · rcases p1453_3 (m.d 0 2) (by simp) with h1458 | h1458
                          · linarith only [h0, h1458, hlam]
                          · linarith only [h1458, h5, hlam]
                        · linarith only [h1457, h2, hlam]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        rcases p1453_3 (m.d 0 1) (by simp) with h1462 | h1462
                        · rcases p1453_3 (m.d 0 2) (by simp) with h1463 | h1463
                          · linarith only [h0, h1463, hlam]
                          · linarith only [h1463, h6, hlam]
                        · linarith only [h1462, h3, hlam]
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
                        linarith only [h1444, h4, h884, hc02, hlam, hphi, ht0b, ht5b, p1453_1, u5ehi3]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        rcases p1453_3 (m.d 0 1) (by simp) with h1470 | h1470
                        · rcases p1453_3 (m.d 0 2) (by simp) with h1471 | h1471
                          · rcases p1453_3 (m.d 0 3) (by simp) with h1472 | h1472
                            · linarith only [h1472, h4, hlam]
                            · linarith only [h1472, h7, hlam]
                          · linarith only [h1471, h5, hlam]
                        · linarith only [h1470, h2, hlam]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        rcases p1453_3 (m.d 0 1) (by simp) with h1477 | h1477
                        · rcases p1453_3 (m.d 0 2) (by simp) with h1478 | h1478
                          · rcases p1453_3 (m.d 0 3) (by simp) with h1479 | h1479
                            · linarith only [h1479, h4, hlam]
                            · linarith only [h1479, h8, hlam]
                          · linarith only [h1478, h6, hlam]
                        · linarith only [h1477, h3, hlam]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        linarith only [h1, hlam, p1453_1]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        linarith only [h4, hlam, p1453_1]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        linarith only [hlam, p1453_0]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        rcases p1453_3 (m.d 0 1) (by simp) with h1487 | h1487
                        · rcases p1453_3 (m.d 0 2) (by simp) with h1488 | h1488
                          · rcases p1453_3 (m.d 0 3) (by simp) with h1489 | h1489
                            · rcases p1453_3 (m.d 0 4) (by simp) with h1490 | h1490
                              · linarith only [h1490, h7, hlam]
                              · rcases p1453_3 (m.d 0 5) (by simp) with h1492 | h1492
                                · linarith only [h1492, h8, hlam]
                                · linarith only [h1492, h9, hlam]
                            · linarith only [h1489, h7, hlam]
                          · linarith only [h1488, h5, hlam]
                        · linarith only [h1487, h2, hlam]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        rcases p1453_3 (m.d 0 1) (by simp) with h1498 | h1498
                        · rcases p1453_3 (m.d 0 2) (by simp) with h1499 | h1499
                          · rcases p1453_3 (m.d 0 3) (by simp) with h1500 | h1500
                            · rcases p1453_3 (m.d 0 4) (by simp) with h1501 | h1501
                              · linarith only [h1501, h7, hlam]
                              · rcases p1453_3 (m.d 0 5) (by simp) with h1503 | h1503
                                · linarith only [h1503, h8, hlam]
                                · rcases h2bigk with h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c | h1505c
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [hlam, p1505_0]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [h1323, h4, h5, h9, hlam, p1453_1, p1505_2]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [h0, h1444, h884, hc01, hlam, hphi, ht0b, ht5b, p1505_1, u5ehi3]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    rcases p1505_3 (m.d 0 2) (by simp) with h1509 | h1509
                                    · rcases p1505_3 (m.d 1 2) (by simp) with h1510 | h1510
                                      · linarith only [h0, h1510, hlam]
                                      · rcases p1505_3 (m.d 2 3) (by simp) with h1512 | h1512
                                        · linarith only [h1512, h4, hlam]
                                        · linarith only [h1447, h1512, hlam]
                                    · linarith only [h1509, hlam, p1505_0]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    rcases p1505_3 (m.d 0 2) (by simp) with h1516 | h1516
                                    · rcases p1505_3 (m.d 1 2) (by simp) with h1517 | h1517
                                      · linarith only [h0, h1517, hlam]
                                      · rcases p1505_3 (m.d 2 3) (by simp) with h1519 | h1519
                                        · linarith only [h1519, h4, hlam]
                                        · linarith only [h1448, h1519, hlam]
                                    · linarith only [h1516, hlam, p1505_0]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [h0, hlam, p1505_0]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [hlam, p1505_0]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [h884, hlam, p1505_0]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [h1323, hlam, p1505_0]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [h1441, hlam, p1505_0]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [h4, hlam, p1505_0]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    rcases p1505_3 (m.d 0 2) (by simp) with h1529 | h1529
                                    · rcases p1505_3 (m.d 1 2) (by simp) with h1530 | h1530
                                      · linarith only [h1530, hlam, p1505_0]
                                      · rcases p1505_3 (m.d 2 3) (by simp) with h1532 | h1532
                                        · rcases p1505_3 (m.d 2 4) (by simp) with h1533 | h1533
                                          · linarith only [h1447, h1533, hlam]
                                          · linarith only [h1323, h1533, hlam]
                                        · linarith only [h1532, hlam, p1505_0]
                                    · linarith only [h0, h1529, hlam]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [hlam, p1505_0]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [h1323, hc12, hc23, hlam, hphi, p1505_1]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p1505_1, u5ehi2]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [h5, hlam, p1505_0]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [h0, h4, h5, h9, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1453_1, p1505_1]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [h1447, hlam, p1505_1]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [hlam, p1505_0]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [h1449, hlam, p1505_1]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [h6, hlam, p1505_0]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [h0, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1453_1, p1505_1]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [h1448, hlam, p1505_1]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [h0, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1453_1, p1505_1]
                                  · have p1505_0 := h1505c.1
                                    have p1505_1 := h1505c.2.1
                                    have p1505_2 := h1505c.2.2.1
                                    have p1505_3 := h1505c.2.2.2
                                    linarith only [hlam, p1505_0]
                            · linarith only [h1500, h8, hlam]
                          · linarith only [h1499, h6, hlam]
                        · linarith only [h1498, h3, hlam]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        linarith only [h2, hlam, p1453_0]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        linarith only [h5, hlam, p1453_0]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        linarith only [h7, hlam, p1453_0]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        linarith only [hlam, p1453_0]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        linarith only [h9, hlam, p1453_0]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        linarith only [h3, hlam, p1453_0]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        linarith only [h6, hlam, p1453_1]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        linarith only [h8, hlam, p1453_0]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        linarith only [h1323, h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p1453_1]
                      · have p1453_0 := h1453c.1
                        have p1453_1 := h1453c.2.1
                        have p1453_2 := h1453c.2.2.1
                        have p1453_3 := h1453c.2.2.2
                        linarith only [hlam, p1453_0]
                · linarith only [h1, h1444, h1448, h884, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h0, h1444, h1447, h4, h7, h884, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1566 | h1566
            · linarith only [h1566, h2, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1568 | h1568
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1569 | h1569
                · linarith only [h0, h1443, h1444, h1569, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1571 | h1571
                  · linarith only [h1571, h5, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1573 | h1573
                    · linarith only [h1, h1443, h1573, h9, hc01, hlam, hphi, ht0b, ht5b, u5ehi0]
                    · rcases h0bigk with h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c | h1575c
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [hlam, p1575_0]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [h1569, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1575_1]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [h1569, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1575_1]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        rcases p1575_3 (m.d 0 1) (by simp) with h1579 | h1579
                        · rcases p1575_3 (m.d 0 2) (by simp) with h1580 | h1580
                          · linarith only [h0, h1580, hlam]
                          · linarith only [h1580, h5, hlam]
                        · linarith only [h1579, h2, hlam]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [h1323, h1568, h1569, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1575_1]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [h0, hlam, p1575_0]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [hlam, p1575_0]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [h1323, h1568, h1569, h8, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1575_1]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        rcases p1575_3 (m.d 0 1) (by simp) with h1588 | h1588
                        · rcases p1575_3 (m.d 0 2) (by simp) with h1589 | h1589
                          · rcases p1575_3 (m.d 0 3) (by simp) with h1590 | h1590
                            · linarith only [h1590, h4, hlam]
                            · linarith only [h1590, h7, hlam]
                          · linarith only [h1589, h5, hlam]
                        · linarith only [h1588, h2, hlam]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [h0, h1323, h1568, h1569, h8, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1575_1]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [h1, hlam, p1575_1]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [h4, hlam, p1575_1]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [hlam, p1575_0]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        rcases p1575_3 (m.d 0 1) (by simp) with h1599 | h1599
                        · rcases p1575_3 (m.d 0 2) (by simp) with h1600 | h1600
                          · rcases p1575_3 (m.d 0 3) (by simp) with h1601 | h1601
                            · rcases p1575_3 (m.d 0 4) (by simp) with h1602 | h1602
                              · linarith only [h1602, h7, hlam]
                              · rcases p1575_3 (m.d 0 5) (by simp) with h1604 | h1604
                                · linarith only [h1604, h8, hlam]
                                · linarith only [h1604, h9, hlam]
                            · linarith only [h1601, h7, hlam]
                          · linarith only [h1600, h5, hlam]
                        · linarith only [h1599, h2, hlam]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [h1323, h1568, h1569, h8, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1575_1]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [h2, hlam, p1575_0]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [h5, hlam, p1575_0]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [h7, hlam, p1575_0]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [hlam, p1575_0]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [h9, hlam, p1575_0]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [h3, hlam, p1575_0]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [h6, hlam, p1575_1]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [h8, hlam, p1575_0]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [h1323, h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p1575_1]
                      · have p1575_0 := h1575c.1
                        have p1575_1 := h1575c.2.1
                        have p1575_2 := h1575c.2.2.1
                        have p1575_3 := h1575c.2.2.2
                        linarith only [hlam, p1575_0]
              · linarith only [h1443, h1444, h1568, hc23, hc35, hlam, hphi]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1622 | h1622
          · linarith only [h1443, h1622, h7, h9, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1624 | h1624
            · linarith only [h1323, h1624, h5, h9, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1626 | h1626
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1627 | h1627
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1628 | h1628
                  · linarith only [h1628, h5, h9, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1630 | h1630
                    · linarith only [h0, h1626, h1630, h4, h9, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h0bigk with h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c | h1632c
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h1622, h1627, h4, hc01, hlam, hphi, ht0b, ht5b, p1632_1, u5ehi1]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h1622, h1627, h4, hc01, hlam, hphi, ht0b, ht5b, p1632_1, u5ehi1]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        rcases p1632_3 (m.d 0 1) (by simp) with h1636 | h1636
                        · rcases p1632_3 (m.d 0 2) (by simp) with h1637 | h1637
                          · linarith only [h0, h1637, hlam]
                          · linarith only [h1637, h5, hlam]
                        · linarith only [h1636, h2, hlam]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        rcases p1632_3 (m.d 0 1) (by simp) with h1641 | h1641
                        · rcases p1632_3 (m.d 0 2) (by simp) with h1642 | h1642
                          · linarith only [h0, h1642, hlam]
                          · linarith only [h1642, h6, hlam]
                        · linarith only [h1641, h3, hlam]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h0, hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h1622, h1627, h4, hc02, hlam, hphi, ht0b, ht5b, p1632_1, u5ehi1]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        rcases p1632_3 (m.d 0 1) (by simp) with h1649 | h1649
                        · rcases p1632_3 (m.d 0 2) (by simp) with h1650 | h1650
                          · rcases p1632_3 (m.d 0 3) (by simp) with h1651 | h1651
                            · linarith only [h1651, h4, hlam]
                            · linarith only [h1651, h7, hlam]
                          · linarith only [h1650, h5, hlam]
                        · linarith only [h1649, h2, hlam]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        rcases p1632_3 (m.d 0 1) (by simp) with h1656 | h1656
                        · rcases p1632_3 (m.d 0 2) (by simp) with h1657 | h1657
                          · rcases p1632_3 (m.d 0 3) (by simp) with h1658 | h1658
                            · linarith only [h1658, h4, hlam]
                            · linarith only [h1658, h8, hlam]
                          · linarith only [h1657, h6, hlam]
                        · linarith only [h1656, h3, hlam]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h1, hlam, p1632_1]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h4, hlam, p1632_1]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        rcases p1632_3 (m.d 0 1) (by simp) with h1666 | h1666
                        · rcases p1632_3 (m.d 0 2) (by simp) with h1667 | h1667
                          · rcases p1632_3 (m.d 0 3) (by simp) with h1668 | h1668
                            · rcases p1632_3 (m.d 0 4) (by simp) with h1669 | h1669
                              · linarith only [h1669, h7, hlam]
                              · rcases p1632_3 (m.d 0 5) (by simp) with h1671 | h1671
                                · linarith only [h1671, h8, hlam]
                                · linarith only [h1671, h9, hlam]
                            · linarith only [h1668, h7, hlam]
                          · linarith only [h1667, h5, hlam]
                        · linarith only [h1666, h2, hlam]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        rcases p1632_3 (m.d 0 1) (by simp) with h1677 | h1677
                        · rcases p1632_3 (m.d 0 2) (by simp) with h1678 | h1678
                          · rcases p1632_3 (m.d 0 3) (by simp) with h1679 | h1679
                            · rcases p1632_3 (m.d 0 4) (by simp) with h1680 | h1680
                              · linarith only [h1680, h7, hlam]
                              · rcases p1632_3 (m.d 0 5) (by simp) with h1682 | h1682
                                · linarith only [h1682, h8, hlam]
                                · rcases h2bigk with h1684c | h1684c | h1684c | h1684c | h1684c | h1684c | h1684c | h1684c | h1684c | h1684c | h1684c | h1684c | h1684c | h1684c | h1684c | h1684c | h1684c | h1684c | h1684c | h1684c | h1684c | h1684c | h1684c | h1684c | h1684c
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [hlam, p1684_0]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [h1443, h1627, h1630, h4, h884, hlam, p1684_2]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [h1443, h1627, h1630, h884, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1684_1]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    rcases p1684_3 (m.d 0 2) (by simp) with h1688 | h1688
                                    · rcases p1684_3 (m.d 1 2) (by simp) with h1689 | h1689
                                      · linarith only [h0, h1689, hlam]
                                      · rcases p1684_3 (m.d 2 3) (by simp) with h1691 | h1691
                                        · linarith only [h1691, h4, hlam]
                                        · linarith only [h1626, h1691, hlam]
                                    · linarith only [h1688, hlam, p1684_0]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    rcases p1684_3 (m.d 0 2) (by simp) with h1695 | h1695
                                    · rcases p1684_3 (m.d 1 2) (by simp) with h1696 | h1696
                                      · linarith only [h0, h1696, hlam]
                                      · rcases p1684_3 (m.d 2 3) (by simp) with h1698 | h1698
                                        · linarith only [h1698, h4, hlam]
                                        · linarith only [h1627, h1698, hlam]
                                    · linarith only [h1695, hlam, p1684_0]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [h0, hlam, p1684_0]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [hlam, p1684_0]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [h884, hlam, p1684_0]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [h1323, hlam, p1684_0]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [h1441, hlam, p1684_0]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [h4, hlam, p1684_0]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    rcases p1684_3 (m.d 0 2) (by simp) with h1708 | h1708
                                    · rcases p1684_3 (m.d 1 2) (by simp) with h1709 | h1709
                                      · linarith only [h1709, hlam, p1684_0]
                                      · rcases p1684_3 (m.d 2 3) (by simp) with h1711 | h1711
                                        · rcases p1684_3 (m.d 2 4) (by simp) with h1712 | h1712
                                          · linarith only [h1626, h1712, hlam]
                                          · linarith only [h1323, h1712, hlam]
                                        · linarith only [h1711, hlam, p1684_0]
                                    · linarith only [h0, h1708, hlam]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [hlam, p1684_0]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [h1443, h1626, h884, hc12, hc23, hlam, hphi, p1684_1]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht5b, p1684_1, u5ehi2]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [h5, hlam, p1684_0]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [h5, h9, hc12, hc45, hlam, hphi, ht23, ht34, p1684_1]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [h1626, hlam, p1684_1]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [hlam, p1684_0]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [h1628, hlam, p1684_1]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [h6, hlam, p1684_0]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [h0, h4, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1632_1, p1684_1]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [h1627, hlam, p1684_1]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [h0, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1632_1, p1684_1]
                                  · have p1684_0 := h1684c.1
                                    have p1684_1 := h1684c.2.1
                                    have p1684_2 := h1684c.2.2.1
                                    have p1684_3 := h1684c.2.2.2
                                    linarith only [hlam, p1684_0]
                            · linarith only [h1679, h8, hlam]
                          · linarith only [h1678, h6, hlam]
                        · linarith only [h1677, h3, hlam]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h2, hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h5, hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h7, hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h9, hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h3, hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h6, hlam, p1632_1]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h8, hlam, p1632_0]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [h1443, h7, h884, h9, hc12, hc45, hlam, hphi, ht23, ht34, p1632_1]
                      · have p1632_0 := h1632c.1
                        have p1632_1 := h1632c.2.1
                        have p1632_2 := h1632c.2.2.1
                        have p1632_3 := h1632c.2.2.2
                        linarith only [hlam, p1632_0]
                · linarith only [h0, h1443, h1626, h1627, h4, h8, h884, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h1626, h7, h884, h9, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6290000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0bigk := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_M_IR_s6_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 h7 h8 h9

end R2N4
