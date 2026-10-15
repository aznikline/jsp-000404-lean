import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_34S8
import Jsp000404.R1LeavesN7_34S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h12 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h377 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h438 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 2 3 4 (by decide) (by decide) with h894 | h894
  · linarith only [h12, h894, h9, hlam]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h896 | h896
    · linarith only [h377, h896, h9, hlam]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h898 | h898
      · linarith only [h0, h10, h438, h898, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h900 | h900
        · rcases h1bigk with h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c | h901c
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            linarith only [hlam, p901_0]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            rcases p901_3 (m.d 0 1) (by simp) with h903 | h903
            · rcases p901_3 (m.d 1 2) (by simp) with h904 | h904
              · linarith only [h904, hlam, p901_0]
              · rcases p901_3 (m.d 1 3) (by simp) with h906 | h906
                · linarith only [h1, h906, hlam]
                · rcases p901_3 (m.d 1 4) (by simp) with h908 | h908
                  · linarith only [h2, h908, hlam]
                  · rcases p901_3 (m.d 1 5) (by simp) with h910 | h910
                    · linarith only [h3, h910, hlam]
                    · rcases h3bigk with h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c | h912c
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [hlam, p912_0]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [h12, h438, h6, h900, hlam, p912_2]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [h12, h438, h6, h9, h900, hlam, p912_2]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [h12, h438, h9, h900, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p912_1]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        rcases p912_3 (m.d 0 3) (by simp) with h917 | h917
                        · rcases p912_3 (m.d 1 3) (by simp) with h918 | h918
                          · linarith only [h1, h918, hlam]
                          · rcases p912_3 (m.d 2 3) (by simp) with h920 | h920
                            · linarith only [h4, h920, hlam]
                            · rcases p912_3 (m.d 3 4) (by simp) with h922 | h922
                              · linarith only [h6, h922, hlam]
                              · linarith only [h900, h922, hlam]
                        · linarith only [h917, hlam, p912_0]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [h1, hlam, p912_0]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [hlam, p912_0]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [h12, h438, h900, hc23, hc34, hlam, hphi, p912_1]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [h12, hlam, p912_0]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [h377, hlam, p912_0]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [h4, hlam, p912_0]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [h9, hlam, p912_0]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [hlam, p912_0]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [h894, hlam, p912_0]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [h896, hlam, p912_0]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [h6, hlam, p912_0]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        rcases p912_3 (m.d 0 3) (by simp) with h937 | h937
                        · rcases p912_3 (m.d 1 3) (by simp) with h938 | h938
                          · linarith only [h938, hlam, p912_0]
                          · rcases p912_3 (m.d 2 3) (by simp) with h940 | h940
                            · linarith only [h894, h940, hlam]
                            · rcases p912_3 (m.d 3 4) (by simp) with h942 | h942
                              · rcases p912_3 (m.d 3 5) (by simp) with h943 | h943
                                · linarith only [h900, h943, hlam]
                                · linarith only [h377, h943, hlam]
                              · linarith only [h942, hlam, p912_0]
                        · linarith only [h1, h937, hlam]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        rcases p912_3 (m.d 0 3) (by simp) with h948 | h948
                        · rcases p912_3 (m.d 1 3) (by simp) with h949 | h949
                          · linarith only [h12, h949, hlam]
                          · linarith only [h9, h949, hlam]
                        · linarith only [h4, h948, hlam]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [hlam, p912_0]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [h0, h12, h4, h438, h6, h900, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p912_1]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [h7, hlam, p912_0]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        rcases p912_3 (m.d 0 3) (by simp) with h956 | h956
                        · rcases p912_3 (m.d 1 3) (by simp) with h957 | h957
                          · linarith only [h957, hlam, p912_0]
                          · rcases p912_3 (m.d 2 3) (by simp) with h959 | h959
                            · linarith only [h896, h959, hlam]
                            · rcases p912_3 (m.d 3 4) (by simp) with h961 | h961
                              · rcases p912_3 (m.d 3 5) (by simp) with h962 | h962
                                · rcases h4bigk with h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c | h963c
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [hlam, p963_0]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    rcases p963_3 (m.d 0 4) (by simp) with h965 | h965
                                    · rcases p963_3 (m.d 1 4) (by simp) with h966 | h966
                                      · linarith only [h2, h966, hlam]
                                      · rcases p963_3 (m.d 2 4) (by simp) with h968 | h968
                                        · linarith only [h5, h968, hlam]
                                        · rcases p963_3 (m.d 3 4) (by simp) with h970 | h970
                                          · linarith only [h6, h970, hlam]
                                          · linarith only [h12, h970, hlam]
                                    · linarith only [h2, h965, hlam]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    rcases p963_3 (m.d 0 4) (by simp) with h974 | h974
                                    · rcases p963_3 (m.d 1 4) (by simp) with h975 | h975
                                      · linarith only [h2, h975, hlam]
                                      · linarith only [h10, h975, hlam]
                                    · linarith only [h5, h974, hlam]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [h12, h438, h9, h900, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p963_1]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    rcases p963_3 (m.d 0 4) (by simp) with h980 | h980
                                    · rcases p963_3 (m.d 1 4) (by simp) with h981 | h981
                                      · linarith only [h2, h981, hlam]
                                      · rcases p963_3 (m.d 2 4) (by simp) with h983 | h983
                                        · linarith only [h5, h983, hlam]
                                        · rcases p963_3 (m.d 3 4) (by simp) with h985 | h985
                                          · linarith only [h6, h985, hlam]
                                          · linarith only [h900, h985, hlam]
                                    · linarith only [h980, hlam, p963_0]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [h2, hlam, p963_1]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [hlam, p963_0]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [h438, h900, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p963_1]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [h12, hlam, p963_1]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [h438, hlam, p963_0]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [h5, hlam, p963_1]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [h10, hlam, p963_1]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [hlam, p963_0]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [h894, hlam, p963_1]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [h898, hlam, p963_0]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [h6, hlam, p963_1]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    rcases p963_3 (m.d 0 4) (by simp) with h1000 | h1000
                                    · rcases p963_3 (m.d 1 4) (by simp) with h1001 | h1001
                                      · linarith only [h1001, h12, hlam]
                                      · rcases p963_3 (m.d 2 4) (by simp) with h1003 | h1003
                                        · linarith only [h1003, h894, hlam]
                                        · rcases p963_3 (m.d 3 4) (by simp) with h1005 | h1005
                                          · rcases p963_3 (m.d 4 5) (by simp) with h1006 | h1006
                                            · linarith only [h1006, h900, hlam]
                                            · linarith only [h1006, h438, hlam]
                                          · linarith only [h1005, h12, hlam]
                                    · linarith only [h1000, h2, hlam]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    rcases p963_3 (m.d 0 4) (by simp) with h1011 | h1011
                                    · rcases p963_3 (m.d 1 4) (by simp) with h1012 | h1012
                                      · linarith only [h1012, h12, hlam]
                                      · linarith only [h10, h1012, hlam]
                                    · linarith only [h1011, h5, hlam]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [hlam, p963_0]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [h0, h12, h4, h438, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p963_1]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [h8, hlam, p963_0]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [h0, h12, h4, h6, h9, h900, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p963_1]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [h0, h4, h6, h894, h900, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p963_1]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [h900, hlam, p963_0]
                                  · have p963_0 := h963c.1
                                    have p963_1 := h963c.2.1
                                    have p963_2 := h963c.2.2.1
                                    have p963_3 := h963c.2.2.2
                                    linarith only [hlam, p963_0]
                                · linarith only [h962, hlam, p912_0]
                              · linarith only [h12, h961, hlam]
                        · linarith only [h1, h956, hlam]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        rcases p912_3 (m.d 0 3) (by simp) with h1026 | h1026
                        · rcases p912_3 (m.d 1 3) (by simp) with h1027 | h1027
                          · linarith only [h1027, h377, hlam]
                          · linarith only [h1027, h9, hlam]
                        · linarith only [h1026, h4, hlam]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [h900, hlam, p912_0]
                      · have p912_0 := h912c.1
                        have p912_1 := h912c.2.1
                        have p912_2 := h912c.2.2.1
                        have p912_3 := h912c.2.2.2
                        linarith only [hlam, p912_0]
            · linarith only [h903, hlam, p901_0]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            linarith only [h0, h12, h4, h438, h6, h900, hlam, p901_2]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            linarith only [h0, h4, h438, h6, h900, hlam, p901_2]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            rcases p901_3 (m.d 0 1) (by simp) with h1036 | h1036
            · rcases p901_3 (m.d 1 2) (by simp) with h1037 | h1037
              · linarith only [h0, h1037, hlam]
              · linarith only [h1037, h11, hlam]
            · linarith only [h1036, hlam, p901_0]
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
            rcases p901_3 (m.d 0 1) (by simp) with h1043 | h1043
            · rcases p901_3 (m.d 1 2) (by simp) with h1044 | h1044
              · rcases p901_3 (m.d 1 3) (by simp) with h1045 | h1045
                · linarith only [h1045, h9, hlam]
                · rcases p901_3 (m.d 1 4) (by simp) with h1047 | h1047
                  · linarith only [h10, h1047, hlam]
                  · linarith only [h1047, h12, hlam]
              · linarith only [h1044, h9, hlam]
            · linarith only [h1, h1043, hlam]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            rcases p901_3 (m.d 0 1) (by simp) with h1052 | h1052
            · rcases p901_3 (m.d 1 2) (by simp) with h1053 | h1053
              · rcases p901_3 (m.d 1 3) (by simp) with h1054 | h1054
                · linarith only [h1054, h9, hlam]
                · rcases p901_3 (m.d 1 4) (by simp) with h1056 | h1056
                  · linarith only [h10, h1056, hlam]
                  · rcases p901_3 (m.d 1 5) (by simp) with h1058 | h1058
                    · linarith only [h1058, h11, hlam]
                    · linarith only [h1058, h438, hlam]
              · linarith only [h10, h1053, hlam]
            · linarith only [h1052, h2, hlam]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            rcases p901_3 (m.d 0 1) (by simp) with h1063 | h1063
            · rcases p901_3 (m.d 1 2) (by simp) with h1064 | h1064
              · rcases p901_3 (m.d 1 3) (by simp) with h1065 | h1065
                · linarith only [h1065, h9, hlam]
                · rcases p901_3 (m.d 1 4) (by simp) with h1067 | h1067
                  · linarith only [h10, h1067, hlam]
                  · rcases p901_3 (m.d 1 5) (by simp) with h1069 | h1069
                    · linarith only [h1069, h11, hlam]
                    · rcases h3bigk with h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [hlam, p1071_0]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [h12, h438, h6, h900, hlam, p1071_2]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [h12, h438, h6, h9, h900, hlam, p1071_2]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [h0, h12, h4, h438, h900, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1071_1]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        rcases p1071_3 (m.d 0 3) (by simp) with h1076 | h1076
                        · rcases p1071_3 (m.d 1 3) (by simp) with h1077 | h1077
                          · linarith only [h1, h1077, hlam]
                          · rcases p1071_3 (m.d 2 3) (by simp) with h1079 | h1079
                            · linarith only [h1079, h4, hlam]
                            · rcases p1071_3 (m.d 3 4) (by simp) with h1081 | h1081
                              · linarith only [h1081, h6, hlam]
                              · linarith only [h1081, h900, hlam]
                        · linarith only [h1076, hlam, p1071_0]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [h1, hlam, p1071_0]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [hlam, p1071_0]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [h12, h438, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1071_1, p901_1]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [h12, hlam, p1071_0]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [h377, hlam, p1071_0]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [h4, hlam, p1071_0]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [h9, hlam, p1071_0]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [hlam, p1071_0]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [h894, hlam, p1071_0]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [h896, hlam, p1071_0]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [h6, hlam, p1071_0]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        rcases p1071_3 (m.d 0 3) (by simp) with h1096 | h1096
                        · rcases p1071_3 (m.d 1 3) (by simp) with h1097 | h1097
                          · linarith only [h1097, hlam, p1071_0]
                          · rcases p1071_3 (m.d 2 3) (by simp) with h1099 | h1099
                            · linarith only [h1099, h894, hlam]
                            · rcases p1071_3 (m.d 3 4) (by simp) with h1101 | h1101
                              · rcases p1071_3 (m.d 3 5) (by simp) with h1102 | h1102
                                · linarith only [h1102, h900, hlam]
                                · linarith only [h1102, h377, hlam]
                              · linarith only [h1101, hlam, p1071_0]
                        · linarith only [h1, h1096, hlam]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        rcases p1071_3 (m.d 0 3) (by simp) with h1107 | h1107
                        · rcases p1071_3 (m.d 1 3) (by simp) with h1108 | h1108
                          · linarith only [h1108, h12, hlam]
                          · linarith only [h1108, h9, hlam]
                        · linarith only [h1107, h4, hlam]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [hlam, p1071_0]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [h0, h12, h4, h438, h6, h9, h900, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1071_1]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [h7, hlam, p1071_0]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        rcases p1071_3 (m.d 0 3) (by simp) with h1115 | h1115
                        · rcases p1071_3 (m.d 1 3) (by simp) with h1116 | h1116
                          · linarith only [h1116, hlam, p1071_0]
                          · rcases p1071_3 (m.d 2 3) (by simp) with h1118 | h1118
                            · linarith only [h1118, h896, hlam]
                            · rcases p1071_3 (m.d 3 4) (by simp) with h1120 | h1120
                              · rcases p1071_3 (m.d 3 5) (by simp) with h1121 | h1121
                                · rcases h4bigk with h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [hlam, p1122_0]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    rcases p1122_3 (m.d 0 4) (by simp) with h1124 | h1124
                                    · rcases p1122_3 (m.d 1 4) (by simp) with h1125 | h1125
                                      · linarith only [h1125, h2, hlam]
                                      · rcases p1122_3 (m.d 2 4) (by simp) with h1127 | h1127
                                        · linarith only [h1127, h5, hlam]
                                        · rcases p1122_3 (m.d 3 4) (by simp) with h1129 | h1129
                                          · linarith only [h1129, h6, hlam]
                                          · linarith only [h1129, h12, hlam]
                                    · linarith only [h1124, h2, hlam]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    rcases p1122_3 (m.d 0 4) (by simp) with h1133 | h1133
                                    · rcases p1122_3 (m.d 1 4) (by simp) with h1134 | h1134
                                      · linarith only [h1134, h2, hlam]
                                      · linarith only [h10, h1134, hlam]
                                    · linarith only [h1133, h5, hlam]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [h12, h438, h9, h900, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1122_1]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    rcases p1122_3 (m.d 0 4) (by simp) with h1139 | h1139
                                    · rcases p1122_3 (m.d 1 4) (by simp) with h1140 | h1140
                                      · linarith only [h1140, h2, hlam]
                                      · rcases p1122_3 (m.d 2 4) (by simp) with h1142 | h1142
                                        · linarith only [h1142, h5, hlam]
                                        · rcases p1122_3 (m.d 3 4) (by simp) with h1144 | h1144
                                          · linarith only [h1144, h6, hlam]
                                          · linarith only [h1144, h900, hlam]
                                    · linarith only [h1139, hlam, p1122_0]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [h2, hlam, p1122_1]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [hlam, p1122_0]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [h438, h900, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1122_1]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [h12, hlam, p1122_1]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [h438, hlam, p1122_0]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [h5, hlam, p1122_1]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [h10, hlam, p1122_1]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [hlam, p1122_0]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [h894, hlam, p1122_1]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [h898, hlam, p1122_0]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [h6, hlam, p1122_1]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    rcases p1122_3 (m.d 0 4) (by simp) with h1159 | h1159
                                    · rcases p1122_3 (m.d 1 4) (by simp) with h1160 | h1160
                                      · linarith only [h1160, h12, hlam]
                                      · rcases p1122_3 (m.d 2 4) (by simp) with h1162 | h1162
                                        · linarith only [h1162, h894, hlam]
                                        · rcases p1122_3 (m.d 3 4) (by simp) with h1164 | h1164
                                          · rcases p1122_3 (m.d 4 5) (by simp) with h1165 | h1165
                                            · linarith only [h1165, h900, hlam]
                                            · linarith only [h1165, h438, hlam]
                                          · linarith only [h1164, h12, hlam]
                                    · linarith only [h1159, h2, hlam]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    rcases p1122_3 (m.d 0 4) (by simp) with h1170 | h1170
                                    · rcases p1122_3 (m.d 1 4) (by simp) with h1171 | h1171
                                      · linarith only [h1171, h12, hlam]
                                      · linarith only [h10, h1171, hlam]
                                    · linarith only [h1170, h5, hlam]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [hlam, p1122_0]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [h0, h12, h4, h438, h6, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1122_1]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [h8, hlam, p1122_0]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [h0, h12, h4, h6, h9, h900, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1122_1]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [h0, h4, h6, h894, h900, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1122_1]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [h900, hlam, p1122_0]
                                  · have p1122_0 := h1122c.1
                                    have p1122_1 := h1122c.2.1
                                    have p1122_2 := h1122c.2.2.1
                                    have p1122_3 := h1122c.2.2.2
                                    linarith only [hlam, p1122_0]
                                · linarith only [h1121, hlam, p1071_0]
                              · linarith only [h1120, h12, hlam]
                        · linarith only [h1, h1115, hlam]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        rcases p1071_3 (m.d 0 3) (by simp) with h1185 | h1185
                        · rcases p1071_3 (m.d 1 3) (by simp) with h1186 | h1186
                          · linarith only [h1186, h377, hlam]
                          · linarith only [h1186, h9, hlam]
                        · linarith only [h1185, h4, hlam]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [h900, hlam, p1071_0]
                      · have p1071_0 := h1071c.1
                        have p1071_1 := h1071c.2.1
                        have p1071_2 := h1071c.2.2.1
                        have p1071_3 := h1071c.2.2.2
                        linarith only [hlam, p1071_0]
              · linarith only [h1064, h11, hlam]
            · linarith only [h1063, h3, hlam]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            linarith only [h1, hlam, p901_0]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            linarith only [h9, hlam, p901_1]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            linarith only [hlam, p901_0]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            linarith only [h12, hlam, p901_1]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            linarith only [h377, hlam, p901_1]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            linarith only [h2, hlam, p901_0]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            linarith only [h10, hlam, p901_1]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            linarith only [h0, h4, h438, h6, h9, h900, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p901_1]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            linarith only [hlam, p901_0]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            linarith only [h438, hlam, p901_1]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            linarith only [h3, hlam, p901_0]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            linarith only [h11, hlam, p901_1]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            linarith only [h0, h4, h438, h6, h9, h900, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p901_1]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            linarith only [h0, h4, h438, h6, h900, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p901_1]
          · have p901_0 := h901c.1
            have p901_1 := h901c.2.1
            have p901_2 := h901c.2.2.1
            have p901_3 := h901c.2.2.2
            linarith only [hlam, p901_0]
        · rcases h1bigk with h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c | h1209c
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            linarith only [hlam, p1209_0]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            rcases p1209_3 (m.d 0 1) (by simp) with h1211 | h1211
            · rcases p1209_3 (m.d 1 2) (by simp) with h1212 | h1212
              · linarith only [h1212, hlam, p1209_0]
              · rcases p1209_3 (m.d 1 3) (by simp) with h1214 | h1214
                · linarith only [h1, h1214, hlam]
                · rcases p1209_3 (m.d 1 4) (by simp) with h1216 | h1216
                  · linarith only [h1216, h2, hlam]
                  · rcases p1209_3 (m.d 1 5) (by simp) with h1218 | h1218
                    · linarith only [h1218, h3, hlam]
                    · rcases h3bigk with h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c | h1220c
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [hlam, p1220_0]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [h12, h6, h8, h900, hlam, p1220_2]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [h12, h6, h8, h9, h900, hlam, p1220_2]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        rcases p1220_3 (m.d 0 3) (by simp) with h1224 | h1224
                        · rcases p1220_3 (m.d 1 3) (by simp) with h1225 | h1225
                          · linarith only [h1, h1225, hlam]
                          · rcases p1220_3 (m.d 2 3) (by simp) with h1227 | h1227
                            · linarith only [h1227, h4, hlam]
                            · rcases p1220_3 (m.d 3 4) (by simp) with h1229 | h1229
                              · linarith only [h1229, hlam, p1220_0]
                              · rcases p1220_3 (m.d 3 5) (by simp) with h1231 | h1231
                                · linarith only [h1231, h7, hlam]
                                · linarith only [h1231, h900, hlam]
                        · linarith only [h1224, hlam, p1220_0]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        rcases p1220_3 (m.d 0 3) (by simp) with h1235 | h1235
                        · rcases p1220_3 (m.d 1 3) (by simp) with h1236 | h1236
                          · linarith only [h1, h1236, hlam]
                          · rcases p1220_3 (m.d 2 3) (by simp) with h1238 | h1238
                            · linarith only [h1238, h4, hlam]
                            · rcases p1220_3 (m.d 3 4) (by simp) with h1240 | h1240
                              · linarith only [h1240, h6, hlam]
                              · rcases p1220_3 (m.d 3 5) (by simp) with h1242 | h1242
                                · linarith only [h1242, hlam, p1220_0]
                                · rcases h4bigk with h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c | h1244c
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [hlam, p1244_0]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    rcases p1244_3 (m.d 0 4) (by simp) with h1246 | h1246
                                    · rcases p1244_3 (m.d 1 4) (by simp) with h1247 | h1247
                                      · linarith only [h1247, h2, hlam]
                                      · rcases p1244_3 (m.d 2 4) (by simp) with h1249 | h1249
                                        · linarith only [h1249, h5, hlam]
                                        · rcases p1244_3 (m.d 3 4) (by simp) with h1251 | h1251
                                          · linarith only [h1251, h6, hlam]
                                          · linarith only [h12, h1251, hlam]
                                    · linarith only [h1246, h2, hlam]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    rcases p1244_3 (m.d 0 4) (by simp) with h1255 | h1255
                                    · rcases p1244_3 (m.d 1 4) (by simp) with h1256 | h1256
                                      · linarith only [h1256, h2, hlam]
                                      · linarith only [h10, h1256, hlam]
                                    · linarith only [h1255, h5, hlam]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    rcases p1244_3 (m.d 0 4) (by simp) with h1260 | h1260
                                    · rcases p1244_3 (m.d 1 4) (by simp) with h1261 | h1261
                                      · linarith only [h1261, h2, hlam]
                                      · rcases p1244_3 (m.d 2 4) (by simp) with h1263 | h1263
                                        · linarith only [h1263, h5, hlam]
                                        · rcases p1244_3 (m.d 3 4) (by simp) with h1265 | h1265
                                          · linarith only [h1265, h6, hlam]
                                          · rcases p1244_3 (m.d 4 5) (by simp) with h1267 | h1267
                                            · linarith only [h1267, h8, hlam]
                                            · linarith only [h1267, h900, hlam]
                                    · linarith only [h1260, h6, hlam]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [h0, h12, h4, h6, h900, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1244_1]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [h2, hlam, p1244_1]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [hlam, p1244_0]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [h10, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1209_1, p1244_1]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [h12, hlam, p1244_1]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [h438, hlam, p1244_0]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [h5, hlam, p1244_1]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [h10, hlam, p1244_1]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [hlam, p1244_0]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [h894, hlam, p1244_1]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [h898, hlam, p1244_0]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [h6, hlam, p1244_1]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [h900, hc14, hc45, hlam, hphi, p1244_1]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [h0, h4, h6, h8, h900, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1244_1]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [hlam, p1244_0]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [h900, hlam, p1244_0]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [h8, hlam, p1244_0]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    rcases p1244_3 (m.d 0 4) (by simp) with h1288 | h1288
                                    · rcases p1244_3 (m.d 1 4) (by simp) with h1289 | h1289
                                      · linarith only [h1289, hlam, p1244_0]
                                      · rcases p1244_3 (m.d 2 4) (by simp) with h1291 | h1291
                                        · linarith only [h1291, h898, hlam]
                                        · rcases p1244_3 (m.d 3 4) (by simp) with h1293 | h1293
                                          · linarith only [h1293, h900, hlam]
                                          · linarith only [h12, h1293, hlam]
                                    · linarith only [h1288, h2, hlam]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    rcases p1244_3 (m.d 0 4) (by simp) with h1297 | h1297
                                    · rcases p1244_3 (m.d 1 4) (by simp) with h1298 | h1298
                                      · linarith only [h1298, h438, hlam]
                                      · linarith only [h10, h1298, hlam]
                                    · linarith only [h1297, h5, hlam]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [h0, h12, h4, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1244_1]
                                  · have p1244_0 := h1244c.1
                                    have p1244_1 := h1244c.2.1
                                    have p1244_2 := h1244c.2.2.1
                                    have p1244_3 := h1244c.2.2.2
                                    linarith only [hlam, p1244_0]
                        · linarith only [h1235, hlam, p1220_0]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [h1, hlam, p1220_0]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [hlam, p1220_0]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1209_1, p1220_1]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [h12, hlam, p1220_0]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [h377, hlam, p1220_0]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [h4, hlam, p1220_0]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [h9, hlam, p1220_0]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [hlam, p1220_0]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [h894, hlam, p1220_0]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [h896, hlam, p1220_0]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [h6, hlam, p1220_0]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [h0, h4, h6, h8, h9, h900, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1220_1]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [h0, h4, h6, h8, h900, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1220_1]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [hlam, p1220_0]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [h900, hlam, p1220_1]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [h7, hlam, p1220_0]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        rcases p1220_3 (m.d 0 3) (by simp) with h1321 | h1321
                        · rcases p1220_3 (m.d 1 3) (by simp) with h1322 | h1322
                          · linarith only [h1322, hlam, p1220_0]
                          · rcases p1220_3 (m.d 2 3) (by simp) with h1324 | h1324
                            · linarith only [h1324, h896, hlam]
                            · rcases p1220_3 (m.d 3 4) (by simp) with h1326 | h1326
                              · linarith only [h1326, h900, hlam]
                              · linarith only [h12, h1326, hlam]
                        · linarith only [h1, h1321, hlam]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        rcases p1220_3 (m.d 0 3) (by simp) with h1330 | h1330
                        · rcases p1220_3 (m.d 1 3) (by simp) with h1331 | h1331
                          · linarith only [h1331, h377, hlam]
                          · linarith only [h1331, h9, hlam]
                        · linarith only [h1330, h4, hlam]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [h0, h12, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1220_1]
                      · have p1220_0 := h1220c.1
                        have p1220_1 := h1220c.2.1
                        have p1220_2 := h1220c.2.2.1
                        have p1220_3 := h1220c.2.2.2
                        linarith only [hlam, p1220_0]
            · linarith only [h1211, hlam, p1209_0]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            linarith only [h0, h12, h4, h6, h8, h900, hlam, p1209_2]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            rcases p1209_3 (m.d 0 1) (by simp) with h1339 | h1339
            · rcases p1209_3 (m.d 1 2) (by simp) with h1340 | h1340
              · linarith only [h0, h1340, hlam]
              · linarith only [h10, h1340, hlam]
            · linarith only [h1339, hlam, p1209_0]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            rcases p1209_3 (m.d 0 1) (by simp) with h1344 | h1344
            · rcases p1209_3 (m.d 1 2) (by simp) with h1345 | h1345
              · linarith only [h0, h1345, hlam]
              · linarith only [h11, h1345, hlam]
            · linarith only [h1344, hlam, p1209_0]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            linarith only [h0, hlam, p1209_0]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            linarith only [hlam, p1209_0]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            rcases p1209_3 (m.d 0 1) (by simp) with h1351 | h1351
            · rcases p1209_3 (m.d 1 2) (by simp) with h1352 | h1352
              · rcases p1209_3 (m.d 1 3) (by simp) with h1353 | h1353
                · linarith only [h1353, h9, hlam]
                · rcases p1209_3 (m.d 1 4) (by simp) with h1355 | h1355
                  · linarith only [h10, h1355, hlam]
                  · linarith only [h12, h1355, hlam]
              · linarith only [h1352, h9, hlam]
            · linarith only [h1, h1351, hlam]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            rcases p1209_3 (m.d 0 1) (by simp) with h1360 | h1360
            · rcases p1209_3 (m.d 1 2) (by simp) with h1361 | h1361
              · rcases p1209_3 (m.d 1 3) (by simp) with h1362 | h1362
                · linarith only [h1362, h9, hlam]
                · rcases p1209_3 (m.d 1 4) (by simp) with h1364 | h1364
                  · linarith only [h10, h1364, hlam]
                  · rcases p1209_3 (m.d 1 5) (by simp) with h1366 | h1366
                    · linarith only [h11, h1366, hlam]
                    · linarith only [h1366, h438, hlam]
              · linarith only [h10, h1361, hlam]
            · linarith only [h1360, h2, hlam]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            rcases p1209_3 (m.d 0 1) (by simp) with h1371 | h1371
            · rcases p1209_3 (m.d 1 2) (by simp) with h1372 | h1372
              · rcases p1209_3 (m.d 1 3) (by simp) with h1373 | h1373
                · linarith only [h1373, h9, hlam]
                · rcases p1209_3 (m.d 1 4) (by simp) with h1375 | h1375
                  · linarith only [h10, h1375, hlam]
                  · rcases p1209_3 (m.d 1 5) (by simp) with h1377 | h1377
                    · linarith only [h11, h1377, hlam]
                    · rcases h3bigk with h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c | h1379c
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [hlam, p1379_0]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [h12, h6, h8, h900, hlam, p1379_2]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [h12, h6, h8, h9, h900, hlam, p1379_2]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        rcases p1379_3 (m.d 0 3) (by simp) with h1383 | h1383
                        · rcases p1379_3 (m.d 1 3) (by simp) with h1384 | h1384
                          · linarith only [h1, h1384, hlam]
                          · rcases p1379_3 (m.d 2 3) (by simp) with h1386 | h1386
                            · linarith only [h1386, h4, hlam]
                            · rcases p1379_3 (m.d 3 4) (by simp) with h1388 | h1388
                              · linarith only [h1388, hlam, p1379_0]
                              · rcases p1379_3 (m.d 3 5) (by simp) with h1390 | h1390
                                · linarith only [h1390, h7, hlam]
                                · linarith only [h1390, h900, hlam]
                        · linarith only [h1383, hlam, p1379_0]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        rcases p1379_3 (m.d 0 3) (by simp) with h1394 | h1394
                        · rcases p1379_3 (m.d 1 3) (by simp) with h1395 | h1395
                          · linarith only [h1, h1395, hlam]
                          · rcases p1379_3 (m.d 2 3) (by simp) with h1397 | h1397
                            · linarith only [h1397, h4, hlam]
                            · rcases p1379_3 (m.d 3 4) (by simp) with h1399 | h1399
                              · linarith only [h1399, h6, hlam]
                              · rcases p1379_3 (m.d 3 5) (by simp) with h1401 | h1401
                                · linarith only [h1401, hlam, p1379_0]
                                · rcases h4bigk with h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c | h1403c
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [hlam, p1403_0]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    rcases p1403_3 (m.d 0 4) (by simp) with h1405 | h1405
                                    · rcases p1403_3 (m.d 1 4) (by simp) with h1406 | h1406
                                      · linarith only [h1406, h2, hlam]
                                      · rcases p1403_3 (m.d 2 4) (by simp) with h1408 | h1408
                                        · linarith only [h1408, h5, hlam]
                                        · rcases p1403_3 (m.d 3 4) (by simp) with h1410 | h1410
                                          · linarith only [h1410, h6, hlam]
                                          · linarith only [h12, h1410, hlam]
                                    · linarith only [h1405, h2, hlam]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    rcases p1403_3 (m.d 0 4) (by simp) with h1414 | h1414
                                    · rcases p1403_3 (m.d 1 4) (by simp) with h1415 | h1415
                                      · linarith only [h1415, h2, hlam]
                                      · linarith only [h10, h1415, hlam]
                                    · linarith only [h1414, h5, hlam]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    rcases p1403_3 (m.d 0 4) (by simp) with h1419 | h1419
                                    · rcases p1403_3 (m.d 1 4) (by simp) with h1420 | h1420
                                      · linarith only [h1420, h2, hlam]
                                      · rcases p1403_3 (m.d 2 4) (by simp) with h1422 | h1422
                                        · linarith only [h1422, h5, hlam]
                                        · rcases p1403_3 (m.d 3 4) (by simp) with h1424 | h1424
                                          · linarith only [h1424, h6, hlam]
                                          · rcases p1403_3 (m.d 4 5) (by simp) with h1426 | h1426
                                            · linarith only [h1426, h8, hlam]
                                            · linarith only [h1426, h900, hlam]
                                    · linarith only [h1419, h6, hlam]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h0, h12, h4, h6, h900, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h2, hlam, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [hlam, p1403_0]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h438, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1209_1, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h12, hlam, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h438, hlam, p1403_0]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h5, hlam, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h10, hlam, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [hlam, p1403_0]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h894, hlam, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h898, hlam, p1403_0]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h6, hlam, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h900, hc14, hc45, hlam, hphi, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h0, h4, h6, h8, h900, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [hlam, p1403_0]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h900, hlam, p1403_0]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h8, hlam, p1403_0]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    rcases p1403_3 (m.d 0 4) (by simp) with h1447 | h1447
                                    · rcases p1403_3 (m.d 1 4) (by simp) with h1448 | h1448
                                      · linarith only [h1448, hlam, p1403_0]
                                      · rcases p1403_3 (m.d 2 4) (by simp) with h1450 | h1450
                                        · linarith only [h1450, h898, hlam]
                                        · rcases p1403_3 (m.d 3 4) (by simp) with h1452 | h1452
                                          · linarith only [h1452, h900, hlam]
                                          · linarith only [h12, h1452, hlam]
                                    · linarith only [h1447, h2, hlam]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    rcases p1403_3 (m.d 0 4) (by simp) with h1456 | h1456
                                    · rcases p1403_3 (m.d 1 4) (by simp) with h1457 | h1457
                                      · linarith only [h1457, h438, hlam]
                                      · linarith only [h10, h1457, hlam]
                                    · linarith only [h1456, h5, hlam]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [h0, h12, h4, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1403_1]
                                  · have p1403_0 := h1403c.1
                                    have p1403_1 := h1403c.2.1
                                    have p1403_2 := h1403c.2.2.1
                                    have p1403_3 := h1403c.2.2.2
                                    linarith only [hlam, p1403_0]
                        · linarith only [h1394, hlam, p1379_0]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [h1, hlam, p1379_0]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [hlam, p1379_0]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [h12, hc23, hc34, hlam, hphi, p1379_1]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [h12, hlam, p1379_0]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [h377, hlam, p1379_0]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [h4, hlam, p1379_0]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [h9, hlam, p1379_0]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [hlam, p1379_0]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [h894, hlam, p1379_0]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [h896, hlam, p1379_0]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [h6, hlam, p1379_0]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [h0, h4, h6, h8, h900, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1379_1]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [h0, h4, h6, h8, h900, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1379_1]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [hlam, p1379_0]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [h900, hlam, p1379_1]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [h7, hlam, p1379_0]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        rcases p1379_3 (m.d 0 3) (by simp) with h1480 | h1480
                        · rcases p1379_3 (m.d 1 3) (by simp) with h1481 | h1481
                          · linarith only [h1481, hlam, p1379_0]
                          · rcases p1379_3 (m.d 2 3) (by simp) with h1483 | h1483
                            · linarith only [h1483, h896, hlam]
                            · rcases p1379_3 (m.d 3 4) (by simp) with h1485 | h1485
                              · linarith only [h1485, h900, hlam]
                              · linarith only [h12, h1485, hlam]
                        · linarith only [h1, h1480, hlam]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        rcases p1379_3 (m.d 0 3) (by simp) with h1489 | h1489
                        · rcases p1379_3 (m.d 1 3) (by simp) with h1490 | h1490
                          · linarith only [h1490, h377, hlam]
                          · linarith only [h1490, h9, hlam]
                        · linarith only [h1489, h4, hlam]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [h12, h9, hc23, hc35, hlam, hphi, p1379_1]
                      · have p1379_0 := h1379c.1
                        have p1379_1 := h1379c.2.1
                        have p1379_2 := h1379c.2.2.1
                        have p1379_3 := h1379c.2.2.2
                        linarith only [hlam, p1379_0]
              · linarith only [h11, h1372, hlam]
            · linarith only [h1371, h3, hlam]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            linarith only [h1, hlam, p1209_0]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            linarith only [h9, hlam, p1209_1]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            linarith only [hlam, p1209_0]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            linarith only [h12, hlam, p1209_1]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            linarith only [h377, hlam, p1209_1]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            linarith only [h2, hlam, p1209_0]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            linarith only [h10, hlam, p1209_1]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            linarith only [h0, h4, h438, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1209_1]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            linarith only [hlam, p1209_0]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            linarith only [h438, hlam, p1209_1]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            linarith only [h3, hlam, p1209_0]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            linarith only [h11, hlam, p1209_1]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            rcases p1209_3 (m.d 0 1) (by simp) with h1510 | h1510
            · rcases p1209_3 (m.d 1 2) (by simp) with h1511 | h1511
              · rcases p1209_3 (m.d 1 3) (by simp) with h1512 | h1512
                · linarith only [h1512, h377, hlam]
                · rcases p1209_3 (m.d 1 4) (by simp) with h1514 | h1514
                  · linarith only [h1514, h438, hlam]
                  · linarith only [h12, h1514, hlam]
              · linarith only [h1511, h9, hlam]
            · linarith only [h1, h1510, hlam]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            rcases p1209_3 (m.d 0 1) (by simp) with h1519 | h1519
            · rcases p1209_3 (m.d 1 2) (by simp) with h1520 | h1520
              · rcases p1209_3 (m.d 1 3) (by simp) with h1521 | h1521
                · linarith only [h1521, h377, hlam]
                · rcases p1209_3 (m.d 1 4) (by simp) with h1523 | h1523
                  · linarith only [h1523, h438, hlam]
                  · rcases p1209_3 (m.d 1 5) (by simp) with h1525 | h1525
                    · rcases h3bigk with h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c | h1526c
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [hlam, p1526_0]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [h12, h6, h8, h900, hlam, p1526_2]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [h10, h377, h6, h8, h894, h900, hlam, p1209_1, p1526_2]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        rcases p1526_3 (m.d 0 3) (by simp) with h1530 | h1530
                        · rcases p1526_3 (m.d 1 3) (by simp) with h1531 | h1531
                          · linarith only [h1, h1531, hlam]
                          · rcases p1526_3 (m.d 2 3) (by simp) with h1533 | h1533
                            · linarith only [h1533, h4, hlam]
                            · rcases p1526_3 (m.d 3 4) (by simp) with h1535 | h1535
                              · linarith only [h1535, hlam, p1526_0]
                              · rcases p1526_3 (m.d 3 5) (by simp) with h1537 | h1537
                                · linarith only [h1537, h7, hlam]
                                · linarith only [h1537, h900, hlam]
                        · linarith only [h1530, hlam, p1526_0]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [h0, h377, h4, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1209_1, p1526_1]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [h1, hlam, p1526_0]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [hlam, p1526_0]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [h0, h12, h4, h6, h8, h900, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1526_1]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [h12, hlam, p1526_0]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [h377, hlam, p1526_0]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [h4, hlam, p1526_0]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [h9, hlam, p1526_0]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [hlam, p1526_0]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [h894, hlam, p1526_0]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [h896, hlam, p1526_0]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [h6, hlam, p1526_0]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [h0, h4, h6, h8, h900, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1526_1]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [h0, h4, h6, h8, h900, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1526_1]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [hlam, p1526_0]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [h900, hlam, p1526_1]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [h7, hlam, p1526_0]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        rcases p1526_3 (m.d 0 3) (by simp) with h1558 | h1558
                        · rcases p1526_3 (m.d 1 3) (by simp) with h1559 | h1559
                          · linarith only [h1559, hlam, p1526_0]
                          · rcases p1526_3 (m.d 2 3) (by simp) with h1561 | h1561
                            · linarith only [h1561, h896, hlam]
                            · rcases p1526_3 (m.d 3 4) (by simp) with h1563 | h1563
                              · linarith only [h1563, h900, hlam]
                              · linarith only [h12, h1563, hlam]
                        · linarith only [h1, h1558, hlam]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        rcases p1526_3 (m.d 0 3) (by simp) with h1567 | h1567
                        · rcases p1526_3 (m.d 1 3) (by simp) with h1568 | h1568
                          · linarith only [h1568, h377, hlam]
                          · linarith only [h1568, h9, hlam]
                        · linarith only [h1567, h4, hlam]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [h12, h9, hc23, hc35, hlam, hphi, p1526_1]
                      · have p1526_0 := h1526c.1
                        have p1526_1 := h1526c.2.1
                        have p1526_2 := h1526c.2.2.1
                        have p1526_3 := h1526c.2.2.2
                        linarith only [hlam, p1526_0]
                    · linarith only [h1525, h438, hlam]
              · linarith only [h10, h1520, hlam]
            · linarith only [h1519, h2, hlam]
          · have p1209_0 := h1209c.1
            have p1209_1 := h1209c.2.1
            have p1209_2 := h1209c.2.2.1
            have p1209_3 := h1209c.2.2.2
            linarith only [hlam, p1209_0]

set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x0_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h12 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h377 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 4 5 (by decide) (by decide) with h438 | h438
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x0_x0_x1_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11 h12 h377 h438
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x0_x0_x1_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11 h12 h377 h438

set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h12 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 5 (by decide) (by decide) with h377 | h377
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x0_x0_x1_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11 h12 h377
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x0_x0_x1_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11 h12 h377

set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 4 (by decide) (by decide) with h12 | h12
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11 h12
  · exact r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 h9 h10 h11 h12

set_option maxHeartbeats 8392000 in
set_option maxHeartbeats 8392000 in
theorem r1l7_20_11_13_14_H_R_L_I_L_I_L_I_s8_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg8 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h11 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  rcases m.htr 1 3 4 (by decide) (by decide) with h1578 | h1578
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1579 | h1579
    · linarith only [h11, h1579, h9, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1581 | h1581
      · linarith only [h10, h11, h1581, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1583 | h1583
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1584 | h1584
          · linarith only [h0, h11, h1579, h1581, h1584, h4, h6, h8, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
          · linarith only [h0, h11, h1583, h1584, h4, h7, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h0, h1578, h1579, h1583, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1588 | h1588
    · linarith only [h10, h11, h1578, h1588, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1590 | h1590
      · linarith only [h10, h11, h1590, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1592 | h1592
        · linarith only [h11, h1578, h1592, h9, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1594 | h1594
          · linarith only [h1588, h1594, h9, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1596 | h1596
            · linarith only [h0, h10, h11, h1590, h1594, h1596, h4, h7, hc01, hc15, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1598 | h1598
              · linarith only [h0, h10, h11, h1596, h1598, h4, h6, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · rcases h1bigk with h1600c | h1600c | h1600c | h1600c | h1600c | h1600c | h1600c | h1600c | h1600c | h1600c | h1600c | h1600c | h1600c | h1600c | h1600c | h1600c | h1600c | h1600c | h1600c | h1600c | h1600c | h1600c | h1600c | h1600c | h1600c
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [hlam, p1600_0]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  rcases p1600_3 (m.d 0 1) (by simp) with h1602 | h1602
                  · rcases p1600_3 (m.d 1 2) (by simp) with h1603 | h1603
                    · linarith only [h1603, hlam, p1600_0]
                    · rcases p1600_3 (m.d 1 3) (by simp) with h1605 | h1605
                      · linarith only [h1, h1605, hlam]
                      · rcases p1600_3 (m.d 1 4) (by simp) with h1607 | h1607
                        · linarith only [h1607, h2, hlam]
                        · rcases p1600_3 (m.d 1 5) (by simp) with h1609 | h1609
                          · linarith only [h1609, h3, hlam]
                          · linarith only [h11, h1609, hlam]
                  · linarith only [h1602, hlam, p1600_0]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [h0, h1578, h1598, h4, h6, h8, hlam, p1600_2]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  rcases p1600_3 (m.d 0 1) (by simp) with h1614 | h1614
                  · rcases p1600_3 (m.d 1 2) (by simp) with h1615 | h1615
                    · linarith only [h0, h1615, hlam]
                    · linarith only [h10, h1615, hlam]
                  · linarith only [h1614, hlam, p1600_0]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  rcases p1600_3 (m.d 0 1) (by simp) with h1619 | h1619
                  · rcases p1600_3 (m.d 1 2) (by simp) with h1620 | h1620
                    · linarith only [h0, h1620, hlam]
                    · rcases p1600_3 (m.d 1 3) (by simp) with h1622 | h1622
                      · linarith only [h1, h1622, hlam]
                      · rcases p1600_3 (m.d 1 4) (by simp) with h1624 | h1624
                        · linarith only [h1624, h2, hlam]
                        · rcases p1600_3 (m.d 1 5) (by simp) with h1626 | h1626
                          · linarith only [h1626, hlam, p1600_0]
                          · rcases h3bigk with h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c | h1628c
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1578, h1598, h6, h8, hlam, p1628_2]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h10, h11, h1592, h1594, h7, hlam, p1628_2]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              rcases p1628_3 (m.d 0 3) (by simp) with h1632 | h1632
                              · rcases p1628_3 (m.d 1 3) (by simp) with h1633 | h1633
                                · linarith only [h1, h1633, hlam]
                                · rcases p1628_3 (m.d 2 3) (by simp) with h1635 | h1635
                                  · linarith only [h1635, h4, hlam]
                                  · rcases p1628_3 (m.d 3 4) (by simp) with h1637 | h1637
                                    · linarith only [h1637, hlam, p1628_0]
                                    · rcases p1628_3 (m.d 3 5) (by simp) with h1639 | h1639
                                      · linarith only [h1639, h7, hlam]
                                      · linarith only [h1598, h1639, hlam]
                              · linarith only [h1632, hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h10, h11, h1592, h1594, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1628_1]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1, hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1578, h1598, h8, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1628_1]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1578, hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1588, hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h4, hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h9, hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1592, hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1594, hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h6, hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1598, h8, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1628_1]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h0, h1598, h4, h6, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1628_1]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1598, hlam, p1628_1]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h7, hlam, p1628_0]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              rcases p1628_3 (m.d 0 3) (by simp) with h1660 | h1660
                              · rcases p1628_3 (m.d 1 3) (by simp) with h1661 | h1661
                                · linarith only [h1661, hlam, p1628_0]
                                · rcases p1628_3 (m.d 2 3) (by simp) with h1663 | h1663
                                  · linarith only [h1594, h1663, hlam]
                                  · rcases p1628_3 (m.d 3 4) (by simp) with h1665 | h1665
                                    · linarith only [h1598, h1665, hlam]
                                    · linarith only [h1578, h1665, hlam]
                              · linarith only [h1, h1660, hlam]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              rcases p1628_3 (m.d 0 3) (by simp) with h1669 | h1669
                              · rcases p1628_3 (m.d 1 3) (by simp) with h1670 | h1670
                                · linarith only [h1588, h1670, hlam]
                                · linarith only [h1670, h9, hlam]
                              · linarith only [h1669, h4, hlam]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [h1578, h9, hc23, hc35, hlam, hphi, p1628_1]
                            · have p1628_0 := h1628c.1
                              have p1628_1 := h1628c.2.1
                              have p1628_2 := h1628c.2.2.1
                              have p1628_3 := h1628c.2.2.2
                              linarith only [hlam, p1628_0]
                  · linarith only [h1619, hlam, p1600_0]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [h0, hlam, p1600_0]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [hlam, p1600_0]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [h0, h11, h1594, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1600_1]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [h0, h10, h11, h1592, h1594, h4, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1600_1]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [h11, hlam, p1600_0]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [h1, hlam, p1600_0]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [h9, hlam, p1600_1]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [hlam, p1600_0]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [h1578, hlam, p1600_1]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [h1588, hlam, p1600_1]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [h2, hlam, p1600_0]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [h10, hlam, p1600_1]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [h0, h1590, h4, h6, h8, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1600_1]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [hlam, p1600_0]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [h1590, hlam, p1600_1]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [h3, hlam, p1600_0]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [h0, h1588, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1600_1]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  rcases p1600_3 (m.d 0 1) (by simp) with h1694 | h1694
                  · rcases p1600_3 (m.d 1 2) (by simp) with h1695 | h1695
                    · linarith only [h11, h1695, hlam]
                    · linarith only [h1695, h9, hlam]
                  · linarith only [h1, h1694, hlam]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  rcases p1600_3 (m.d 0 1) (by simp) with h1699 | h1699
                  · rcases p1600_3 (m.d 1 2) (by simp) with h1700 | h1700
                    · linarith only [h11, h1700, hlam]
                    · linarith only [h10, h1700, hlam]
                  · linarith only [h1699, h2, hlam]
                · have p1600_0 := h1600c.1
                  have p1600_1 := h1600c.2.1
                  have p1600_2 := h1600c.2.2.1
                  have p1600_3 := h1600c.2.2.2
                  linarith only [hlam, p1600_0]

end R2N4
