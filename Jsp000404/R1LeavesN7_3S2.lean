import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_3S0
import Jsp000404.R1LeavesN7_3S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x0_x0_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h378 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
    (h439 : (m.d 4 5 + m.lam ≤ m.d 1 4 ∧ m.d 4 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 2 3 4 (by decide) (by decide) with h865 | h865
  · linarith only [h10, h13, h865, hlam]
  · rcases m.htr 2 3 5 (by decide) (by decide) with h867 | h867
    · linarith only [h10, h378, h867, hlam]
    · rcases m.htr 2 4 5 (by decide) (by decide) with h869 | h869
      · linarith only [h0, h11, h439, h869, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
      · rcases m.htr 3 4 5 (by decide) (by decide) with h871 | h871
        · rcases h1bigk with h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c | h872c
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [hlam, p872_0]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            rcases p872_3 (m.d 0 1) (by simp) with h874 | h874
            · rcases p872_3 (m.d 1 2) (by simp) with h875 | h875
              · linarith only [h875, hlam, p872_0]
              · rcases p872_3 (m.d 1 3) (by simp) with h877 | h877
                · linarith only [h1, h877, hlam]
                · rcases p872_3 (m.d 1 4) (by simp) with h879 | h879
                  · linarith only [h2, h879, hlam]
                  · rcases p872_3 (m.d 1 5) (by simp) with h881 | h881
                    · linarith only [h3, h881, hlam]
                    · rcases h3bigk with h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c | h883c
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [hlam, p883_0]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [h13, h439, h7, h871, hlam, p883_2]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [h10, h13, h439, h7, h871, hlam, p883_2]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [h0, h13, h4, h439, h871, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p883_1]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        rcases p883_3 (m.d 0 3) (by simp) with h888 | h888
                        · rcases p883_3 (m.d 1 3) (by simp) with h889 | h889
                          · linarith only [h1, h889, hlam]
                          · rcases p883_3 (m.d 2 3) (by simp) with h891 | h891
                            · linarith only [h4, h891, hlam]
                            · rcases p883_3 (m.d 3 4) (by simp) with h893 | h893
                              · linarith only [h7, h893, hlam]
                              · linarith only [h871, h893, hlam]
                        · linarith only [h888, hlam, p883_0]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [h1, hlam, p883_0]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [hlam, p883_0]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [h13, h439, h871, hc23, hc34, hlam, hphi, p883_1]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [h13, hlam, p883_0]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [h378, hlam, p883_0]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [h4, hlam, p883_0]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [h10, hlam, p883_0]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [hlam, p883_0]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [h865, hlam, p883_0]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [h867, hlam, p883_0]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [h7, hlam, p883_0]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        rcases p883_3 (m.d 0 3) (by simp) with h908 | h908
                        · rcases p883_3 (m.d 1 3) (by simp) with h909 | h909
                          · linarith only [h909, hlam, p883_0]
                          · rcases p883_3 (m.d 2 3) (by simp) with h911 | h911
                            · linarith only [h865, h911, hlam]
                            · rcases p883_3 (m.d 3 4) (by simp) with h913 | h913
                              · rcases p883_3 (m.d 3 5) (by simp) with h914 | h914
                                · linarith only [h871, h914, hlam]
                                · linarith only [h378, h914, hlam]
                              · linarith only [h913, hlam, p883_0]
                        · linarith only [h1, h908, hlam]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        rcases p883_3 (m.d 0 3) (by simp) with h919 | h919
                        · rcases p883_3 (m.d 1 3) (by simp) with h920 | h920
                          · linarith only [h13, h920, hlam]
                          · linarith only [h10, h920, hlam]
                        · linarith only [h4, h919, hlam]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [hlam, p883_0]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [h0, h13, h4, h439, h7, h871, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p883_1]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [h8, hlam, p883_0]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        rcases p883_3 (m.d 0 3) (by simp) with h927 | h927
                        · rcases p883_3 (m.d 1 3) (by simp) with h928 | h928
                          · linarith only [h928, hlam, p883_0]
                          · rcases p883_3 (m.d 2 3) (by simp) with h930 | h930
                            · linarith only [h867, h930, hlam]
                            · rcases p883_3 (m.d 3 4) (by simp) with h932 | h932
                              · rcases p883_3 (m.d 3 5) (by simp) with h933 | h933
                                · rcases h5bigk with h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c | h934c
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [hlam, p934_0]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    rcases p934_3 (m.d 0 5) (by simp) with h936 | h936
                                    · rcases p934_3 (m.d 1 5) (by simp) with h937 | h937
                                      · linarith only [h3, h937, hlam]
                                      · rcases p934_3 (m.d 2 5) (by simp) with h939 | h939
                                        · linarith only [h6, h939, hlam]
                                        · rcases p934_3 (m.d 3 5) (by simp) with h941 | h941
                                          · linarith only [h8, h941, hlam]
                                          · linarith only [h378, h941, hlam]
                                    · linarith only [h3, h936, hlam]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    rcases p934_3 (m.d 0 5) (by simp) with h945 | h945
                                    · rcases p934_3 (m.d 1 5) (by simp) with h946 | h946
                                      · linarith only [h3, h946, hlam]
                                      · linarith only [h12, h946, hlam]
                                    · linarith only [h6, h945, hlam]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [h0, h10, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p883_1, p934_1]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [h0, h10, h13, h4, h439, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p934_1]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [h3, hlam, p934_0]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [hlam, p934_0]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [h3, h865, h869, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p934_1]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [h378, hlam, p934_1]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [h439, hlam, p934_1]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [h6, hlam, p934_1]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [h12, hlam, p934_1]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [hlam, p934_0]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [h867, hlam, p934_1]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [h869, hlam, p934_1]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [h8, hlam, p934_0]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [h0, h4, h8, hc01, hc15, hlam, hphi, ht0b, ht5b, p934_1]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [h0, h4, h8, h865, h869, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p934_1]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [hlam, p934_0]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [h0, h10, h13, h4, h439, h7, h871, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p934_1]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [h9, hlam, p934_0]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [h12, h865, h869, hc23, hc45, hlam, hphi, ht34, p934_1]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [h0, h4, h7, h865, h869, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p934_1]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [h871, hlam, p934_0]
                                  · have p934_0 := h934c.1
                                    have p934_1 := h934c.2.1
                                    have p934_2 := h934c.2.2.1
                                    have p934_3 := h934c.2.2.2
                                    linarith only [hlam, p934_0]
                                · linarith only [h933, hlam, p883_0]
                              · linarith only [h13, h932, hlam]
                        · linarith only [h1, h927, hlam]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        rcases p883_3 (m.d 0 3) (by simp) with h975 | h975
                        · rcases p883_3 (m.d 1 3) (by simp) with h976 | h976
                          · linarith only [h378, h976, hlam]
                          · linarith only [h10, h976, hlam]
                        · linarith only [h4, h975, hlam]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [h871, hlam, p883_0]
                      · have p883_0 := h883c.1
                        have p883_1 := h883c.2.1
                        have p883_2 := h883c.2.2.1
                        have p883_3 := h883c.2.2.2
                        linarith only [hlam, p883_0]
            · linarith only [h874, hlam, p872_0]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [h0, h13, h4, h439, h7, h871, hlam, p872_2]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [h0, h4, h439, h7, h871, hlam, p872_2]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            rcases p872_3 (m.d 0 1) (by simp) with h985 | h985
            · rcases p872_3 (m.d 1 2) (by simp) with h986 | h986
              · linarith only [h0, h986, hlam]
              · linarith only [h12, h986, hlam]
            · linarith only [h985, hlam, p872_0]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [h0, hlam, p872_0]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [hlam, p872_0]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            rcases p872_3 (m.d 0 1) (by simp) with h992 | h992
            · rcases p872_3 (m.d 1 2) (by simp) with h993 | h993
              · rcases p872_3 (m.d 1 3) (by simp) with h994 | h994
                · linarith only [h10, h994, hlam]
                · rcases p872_3 (m.d 1 4) (by simp) with h996 | h996
                  · linarith only [h11, h996, hlam]
                  · linarith only [h13, h996, hlam]
              · linarith only [h10, h993, hlam]
            · linarith only [h1, h992, hlam]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            rcases p872_3 (m.d 0 1) (by simp) with h1001 | h1001
            · rcases p872_3 (m.d 1 2) (by simp) with h1002 | h1002
              · rcases p872_3 (m.d 1 3) (by simp) with h1003 | h1003
                · linarith only [h10, h1003, hlam]
                · rcases p872_3 (m.d 1 4) (by simp) with h1005 | h1005
                  · linarith only [h1005, h11, hlam]
                  · rcases p872_3 (m.d 1 5) (by simp) with h1007 | h1007
                    · linarith only [h1007, h12, hlam]
                    · linarith only [h1007, h439, hlam]
              · linarith only [h1002, h11, hlam]
            · linarith only [h1001, h2, hlam]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            rcases p872_3 (m.d 0 1) (by simp) with h1012 | h1012
            · rcases p872_3 (m.d 1 2) (by simp) with h1013 | h1013
              · rcases p872_3 (m.d 1 3) (by simp) with h1014 | h1014
                · linarith only [h10, h1014, hlam]
                · rcases p872_3 (m.d 1 4) (by simp) with h1016 | h1016
                  · linarith only [h1016, h11, hlam]
                  · rcases p872_3 (m.d 1 5) (by simp) with h1018 | h1018
                    · linarith only [h1018, h12, hlam]
                    · rcases h3bigk with h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [hlam, p1020_0]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [h13, h439, h7, h871, hlam, p1020_2]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [h11, h439, h7, h865, h871, hlam, p1020_2]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [h0, h4, h439, h871, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1020_1]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        rcases p1020_3 (m.d 0 3) (by simp) with h1025 | h1025
                        · rcases p1020_3 (m.d 1 3) (by simp) with h1026 | h1026
                          · linarith only [h1, h1026, hlam]
                          · rcases p1020_3 (m.d 2 3) (by simp) with h1028 | h1028
                            · linarith only [h1028, h4, hlam]
                            · rcases p1020_3 (m.d 3 4) (by simp) with h1030 | h1030
                              · linarith only [h1030, h7, hlam]
                              · linarith only [h1030, h871, hlam]
                        · linarith only [h1025, hlam, p1020_0]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [h1, hlam, p1020_0]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [hlam, p1020_0]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [h13, hc23, hc34, hlam, hphi, p1020_1]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [h13, hlam, p1020_0]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [h378, hlam, p1020_0]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [h4, hlam, p1020_0]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [h10, hlam, p1020_0]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [hlam, p1020_0]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [h865, hlam, p1020_0]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [h867, hlam, p1020_0]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [h7, hlam, p1020_0]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        rcases p1020_3 (m.d 0 3) (by simp) with h1045 | h1045
                        · rcases p1020_3 (m.d 1 3) (by simp) with h1046 | h1046
                          · linarith only [h1046, hlam, p1020_0]
                          · rcases p1020_3 (m.d 2 3) (by simp) with h1048 | h1048
                            · linarith only [h1048, h865, hlam]
                            · rcases p1020_3 (m.d 3 4) (by simp) with h1050 | h1050
                              · rcases p1020_3 (m.d 3 5) (by simp) with h1051 | h1051
                                · linarith only [h1051, h871, hlam]
                                · linarith only [h1051, h378, hlam]
                              · linarith only [h1050, hlam, p1020_0]
                        · linarith only [h1, h1045, hlam]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        rcases p1020_3 (m.d 0 3) (by simp) with h1056 | h1056
                        · rcases p1020_3 (m.d 1 3) (by simp) with h1057 | h1057
                          · linarith only [h1057, h13, hlam]
                          · linarith only [h10, h1057, hlam]
                        · linarith only [h1056, h4, hlam]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [hlam, p1020_0]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [h0, h378, h4, h7, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1020_1]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [h8, hlam, p1020_0]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        rcases p1020_3 (m.d 0 3) (by simp) with h1064 | h1064
                        · rcases p1020_3 (m.d 1 3) (by simp) with h1065 | h1065
                          · linarith only [h1065, hlam, p1020_0]
                          · rcases p1020_3 (m.d 2 3) (by simp) with h1067 | h1067
                            · linarith only [h1067, h867, hlam]
                            · rcases p1020_3 (m.d 3 4) (by simp) with h1069 | h1069
                              · rcases p1020_3 (m.d 3 5) (by simp) with h1070 | h1070
                                · rcases h5bigk with h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c | h1071c
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [hlam, p1071_0]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    rcases p1071_3 (m.d 0 5) (by simp) with h1073 | h1073
                                    · rcases p1071_3 (m.d 1 5) (by simp) with h1074 | h1074
                                      · linarith only [h1074, h3, hlam]
                                      · rcases p1071_3 (m.d 2 5) (by simp) with h1076 | h1076
                                        · linarith only [h1076, h6, hlam]
                                        · rcases p1071_3 (m.d 3 5) (by simp) with h1078 | h1078
                                          · linarith only [h1078, h8, hlam]
                                          · linarith only [h1078, h378, hlam]
                                    · linarith only [h1073, h3, hlam]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    rcases p1071_3 (m.d 0 5) (by simp) with h1082 | h1082
                                    · rcases p1071_3 (m.d 1 5) (by simp) with h1083 | h1083
                                      · linarith only [h1083, h3, hlam]
                                      · linarith only [h1083, h12, hlam]
                                    · linarith only [h1082, h6, hlam]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [h0, h10, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1020_1, p1071_1]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [h0, h11, h4, h439, h7, h865, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1071_1]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [h3, hlam, p1071_0]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [hlam, p1071_0]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [h865, h869, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1071_1, p872_1]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [h378, hlam, p1071_1]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [h439, hlam, p1071_1]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [h6, hlam, p1071_1]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [h12, hlam, p1071_1]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [hlam, p1071_0]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [h867, hlam, p1071_1]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [h869, hlam, p1071_1]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [h8, hlam, p1071_0]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [h0, h4, h8, hc01, hc15, hlam, hphi, ht0b, ht5b, p1071_1]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [h0, h4, h8, h865, h869, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1071_1]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [hlam, p1071_0]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [h0, h11, h4, h439, h7, h865, h871, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1071_1]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [h9, hlam, p1071_0]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [h12, h865, h869, hc23, hc45, hlam, hphi, ht34, p1071_1]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [h0, h4, h7, h865, h869, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1071_1]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [h871, hlam, p1071_0]
                                  · have p1071_0 := h1071c.1
                                    have p1071_1 := h1071c.2.1
                                    have p1071_2 := h1071c.2.2.1
                                    have p1071_3 := h1071c.2.2.2
                                    linarith only [hlam, p1071_0]
                                · linarith only [h1070, hlam, p1020_0]
                              · linarith only [h1069, h13, hlam]
                        · linarith only [h1, h1064, hlam]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        rcases p1020_3 (m.d 0 3) (by simp) with h1112 | h1112
                        · rcases p1020_3 (m.d 1 3) (by simp) with h1113 | h1113
                          · linarith only [h1113, h378, hlam]
                          · linarith only [h10, h1113, hlam]
                        · linarith only [h1112, h4, hlam]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [h871, hlam, p1020_0]
                      · have p1020_0 := h1020c.1
                        have p1020_1 := h1020c.2.1
                        have p1020_2 := h1020c.2.2.1
                        have p1020_3 := h1020c.2.2.2
                        linarith only [hlam, p1020_0]
              · linarith only [h1013, h12, hlam]
            · linarith only [h1012, h3, hlam]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [h1, hlam, p872_0]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [h10, hlam, p872_1]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [hlam, p872_0]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [h13, hlam, p872_1]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [h378, hlam, p872_1]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [h2, hlam, p872_0]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [h11, hlam, p872_1]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [h0, h10, h4, h439, h7, h871, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p872_1]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [hlam, p872_0]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [h439, hlam, p872_1]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [h3, hlam, p872_0]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [h12, hlam, p872_1]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [h0, h10, h4, h439, h7, h871, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p872_1]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [h0, h4, h439, h7, h871, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p872_1]
          · have p872_0 := h872c.1
            have p872_1 := h872c.2.1
            have p872_2 := h872c.2.2.1
            have p872_3 := h872c.2.2.2
            linarith only [hlam, p872_0]
        · rcases h1bigk with h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            linarith only [hlam, p1136_0]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            rcases p1136_3 (m.d 0 1) (by simp) with h1138 | h1138
            · rcases p1136_3 (m.d 1 2) (by simp) with h1139 | h1139
              · linarith only [h1139, hlam, p1136_0]
              · rcases p1136_3 (m.d 1 3) (by simp) with h1141 | h1141
                · linarith only [h1, h1141, hlam]
                · rcases p1136_3 (m.d 1 4) (by simp) with h1143 | h1143
                  · linarith only [h1143, h2, hlam]
                  · rcases p1136_3 (m.d 1 5) (by simp) with h1145 | h1145
                    · linarith only [h1145, h3, hlam]
                    · rcases h3bigk with h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [hlam, p1147_0]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [h13, h7, h871, h9, hlam, p1147_2]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [h10, h13, h7, h871, h9, hlam, p1147_2]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        rcases p1147_3 (m.d 0 3) (by simp) with h1151 | h1151
                        · rcases p1147_3 (m.d 1 3) (by simp) with h1152 | h1152
                          · linarith only [h1, h1152, hlam]
                          · rcases p1147_3 (m.d 2 3) (by simp) with h1154 | h1154
                            · linarith only [h1154, h4, hlam]
                            · rcases p1147_3 (m.d 3 4) (by simp) with h1156 | h1156
                              · linarith only [h1156, hlam, p1147_0]
                              · rcases p1147_3 (m.d 3 5) (by simp) with h1158 | h1158
                                · linarith only [h1158, h8, hlam]
                                · linarith only [h1158, h871, hlam]
                        · linarith only [h1151, hlam, p1147_0]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        rcases p1147_3 (m.d 0 3) (by simp) with h1162 | h1162
                        · rcases p1147_3 (m.d 1 3) (by simp) with h1163 | h1163
                          · linarith only [h1, h1163, hlam]
                          · rcases p1147_3 (m.d 2 3) (by simp) with h1165 | h1165
                            · linarith only [h1165, h4, hlam]
                            · rcases p1147_3 (m.d 3 4) (by simp) with h1167 | h1167
                              · linarith only [h1167, h7, hlam]
                              · rcases p1147_3 (m.d 3 5) (by simp) with h1169 | h1169
                                · linarith only [h1169, hlam, p1147_0]
                                · rcases h5bigk with h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c | h1171c
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [hlam, p1171_0]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    rcases p1171_3 (m.d 0 5) (by simp) with h1173 | h1173
                                    · rcases p1171_3 (m.d 1 5) (by simp) with h1174 | h1174
                                      · linarith only [h1174, h3, hlam]
                                      · rcases p1171_3 (m.d 2 5) (by simp) with h1176 | h1176
                                        · linarith only [h1176, h6, hlam]
                                        · rcases p1171_3 (m.d 3 5) (by simp) with h1178 | h1178
                                          · linarith only [h1178, h8, hlam]
                                          · linarith only [h1178, h378, hlam]
                                    · linarith only [h1173, h3, hlam]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    rcases p1171_3 (m.d 0 5) (by simp) with h1182 | h1182
                                    · rcases p1171_3 (m.d 1 5) (by simp) with h1183 | h1183
                                      · linarith only [h1183, h3, hlam]
                                      · linarith only [h1183, h12, hlam]
                                    · linarith only [h1182, h6, hlam]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [h7, h9, hlam, p1147_2, p1171_1]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [h10, h13, h7, h871, h9, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1171_1]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [h3, hlam, p1171_0]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [hlam, p1171_0]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [h3, h865, h869, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1171_1]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [h378, hlam, p1171_1]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [h439, hlam, p1171_1]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [h6, hlam, p1171_1]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [h12, hlam, p1171_1]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [hlam, p1171_0]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [h867, hlam, p1171_1]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [h869, hlam, p1171_1]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [h8, hlam, p1171_0]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [h0, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p1147_1, p1171_1]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [h0, h4, h865, h869, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1147_1, p1171_1]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [hlam, p1171_0]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [h871, hlam, p1171_1]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [h9, hlam, p1171_0]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [h12, h865, h869, hc23, hc45, hlam, hphi, ht34, p1171_1]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [h0, h4, h7, h865, h869, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1171_1]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [h0, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p1171_1]
                                  · have p1171_0 := h1171c.1
                                    have p1171_1 := h1171c.2.1
                                    have p1171_2 := h1171c.2.2.1
                                    have p1171_3 := h1171c.2.2.2
                                    linarith only [hlam, p1171_0]
                        · linarith only [h1162, hlam, p1147_0]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [h1, hlam, p1147_0]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [hlam, p1147_0]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [h13, hc23, hc34, hlam, hphi, p1147_1]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [h13, hlam, p1147_0]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [h378, hlam, p1147_0]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [h4, hlam, p1147_0]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [h10, hlam, p1147_0]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [hlam, p1147_0]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [h865, hlam, p1147_0]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [h867, hlam, p1147_0]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [h7, hlam, p1147_0]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [h0, h4, h7, h871, h9, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1147_1]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [h0, h4, h7, h871, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1147_1]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [hlam, p1147_0]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [h871, hlam, p1147_1]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [h8, hlam, p1147_0]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        rcases p1147_3 (m.d 0 3) (by simp) with h1226 | h1226
                        · rcases p1147_3 (m.d 1 3) (by simp) with h1227 | h1227
                          · linarith only [h1227, hlam, p1147_0]
                          · rcases p1147_3 (m.d 2 3) (by simp) with h1229 | h1229
                            · linarith only [h1229, h867, hlam]
                            · rcases p1147_3 (m.d 3 4) (by simp) with h1231 | h1231
                              · linarith only [h1231, h871, hlam]
                              · linarith only [h1231, h13, hlam]
                        · linarith only [h1, h1226, hlam]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        rcases p1147_3 (m.d 0 3) (by simp) with h1235 | h1235
                        · rcases p1147_3 (m.d 1 3) (by simp) with h1236 | h1236
                          · linarith only [h1236, h378, hlam]
                          · linarith only [h10, h1236, hlam]
                        · linarith only [h1235, h4, hlam]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [h10, h13, hc23, hc35, hlam, hphi, p1147_1]
                      · have p1147_0 := h1147c.1
                        have p1147_1 := h1147c.2.1
                        have p1147_2 := h1147c.2.2.1
                        have p1147_3 := h1147c.2.2.2
                        linarith only [hlam, p1147_0]
            · linarith only [h1138, hlam, p1136_0]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            linarith only [h0, h13, h4, h7, h871, h9, hlam, p1136_2]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            rcases p1136_3 (m.d 0 1) (by simp) with h1244 | h1244
            · rcases p1136_3 (m.d 1 2) (by simp) with h1245 | h1245
              · linarith only [h0, h1245, hlam]
              · linarith only [h11, h1245, hlam]
            · linarith only [h1244, hlam, p1136_0]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            rcases p1136_3 (m.d 0 1) (by simp) with h1249 | h1249
            · rcases p1136_3 (m.d 1 2) (by simp) with h1250 | h1250
              · linarith only [h0, h1250, hlam]
              · linarith only [h12, h1250, hlam]
            · linarith only [h1249, hlam, p1136_0]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            linarith only [h0, hlam, p1136_0]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            linarith only [hlam, p1136_0]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            rcases p1136_3 (m.d 0 1) (by simp) with h1256 | h1256
            · rcases p1136_3 (m.d 1 2) (by simp) with h1257 | h1257
              · rcases p1136_3 (m.d 1 3) (by simp) with h1258 | h1258
                · linarith only [h10, h1258, hlam]
                · rcases p1136_3 (m.d 1 4) (by simp) with h1260 | h1260
                  · linarith only [h11, h1260, hlam]
                  · linarith only [h1260, h13, hlam]
              · linarith only [h10, h1257, hlam]
            · linarith only [h1, h1256, hlam]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            rcases p1136_3 (m.d 0 1) (by simp) with h1265 | h1265
            · rcases p1136_3 (m.d 1 2) (by simp) with h1266 | h1266
              · rcases p1136_3 (m.d 1 3) (by simp) with h1267 | h1267
                · linarith only [h10, h1267, hlam]
                · rcases p1136_3 (m.d 1 4) (by simp) with h1269 | h1269
                  · linarith only [h11, h1269, hlam]
                  · rcases p1136_3 (m.d 1 5) (by simp) with h1271 | h1271
                    · linarith only [h12, h1271, hlam]
                    · linarith only [h1271, h439, hlam]
              · linarith only [h11, h1266, hlam]
            · linarith only [h1265, h2, hlam]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            rcases p1136_3 (m.d 0 1) (by simp) with h1276 | h1276
            · rcases p1136_3 (m.d 1 2) (by simp) with h1277 | h1277
              · rcases p1136_3 (m.d 1 3) (by simp) with h1278 | h1278
                · linarith only [h10, h1278, hlam]
                · rcases p1136_3 (m.d 1 4) (by simp) with h1280 | h1280
                  · linarith only [h11, h1280, hlam]
                  · rcases p1136_3 (m.d 1 5) (by simp) with h1282 | h1282
                    · linarith only [h12, h1282, hlam]
                    · rcases h3bigk with h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c | h1284c
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [hlam, p1284_0]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [h13, h7, h871, h9, hlam, p1284_2]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [h10, h13, h7, h871, h9, hlam, p1284_2]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        rcases p1284_3 (m.d 0 3) (by simp) with h1288 | h1288
                        · rcases p1284_3 (m.d 1 3) (by simp) with h1289 | h1289
                          · linarith only [h1, h1289, hlam]
                          · rcases p1284_3 (m.d 2 3) (by simp) with h1291 | h1291
                            · linarith only [h1291, h4, hlam]
                            · rcases p1284_3 (m.d 3 4) (by simp) with h1293 | h1293
                              · linarith only [h1293, hlam, p1284_0]
                              · rcases p1284_3 (m.d 3 5) (by simp) with h1295 | h1295
                                · linarith only [h1295, h8, hlam]
                                · linarith only [h1295, h871, hlam]
                        · linarith only [h1288, hlam, p1284_0]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        rcases p1284_3 (m.d 0 3) (by simp) with h1299 | h1299
                        · rcases p1284_3 (m.d 1 3) (by simp) with h1300 | h1300
                          · linarith only [h1, h1300, hlam]
                          · rcases p1284_3 (m.d 2 3) (by simp) with h1302 | h1302
                            · linarith only [h1302, h4, hlam]
                            · rcases p1284_3 (m.d 3 4) (by simp) with h1304 | h1304
                              · linarith only [h1304, h7, hlam]
                              · rcases p1284_3 (m.d 3 5) (by simp) with h1306 | h1306
                                · linarith only [h1306, hlam, p1284_0]
                                · rcases h5bigk with h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c | h1308c
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [hlam, p1308_0]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    rcases p1308_3 (m.d 0 5) (by simp) with h1310 | h1310
                                    · rcases p1308_3 (m.d 1 5) (by simp) with h1311 | h1311
                                      · linarith only [h1311, h3, hlam]
                                      · rcases p1308_3 (m.d 2 5) (by simp) with h1313 | h1313
                                        · linarith only [h1313, h6, hlam]
                                        · rcases p1308_3 (m.d 3 5) (by simp) with h1315 | h1315
                                          · linarith only [h1315, h8, hlam]
                                          · linarith only [h1315, h378, hlam]
                                    · linarith only [h1310, h3, hlam]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    rcases p1308_3 (m.d 0 5) (by simp) with h1319 | h1319
                                    · rcases p1308_3 (m.d 1 5) (by simp) with h1320 | h1320
                                      · linarith only [h1320, h3, hlam]
                                      · linarith only [h12, h1320, hlam]
                                    · linarith only [h1319, h6, hlam]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [h7, h9, hlam, p1284_2, p1308_1]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [h0, h4, h7, h871, h9, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1308_1]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [h3, hlam, p1308_0]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [hlam, p1308_0]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [h3, h865, h869, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1308_1]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [h378, hlam, p1308_1]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [h439, hlam, p1308_1]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [h6, hlam, p1308_1]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [h12, hlam, p1308_1]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [hlam, p1308_0]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [h867, hlam, p1308_1]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [h869, hlam, p1308_1]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [h8, hlam, p1308_0]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [h0, h4, hc01, hc15, hlam, hphi, ht0b, ht5b, p1284_1, p1308_1]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [h0, h4, h865, h869, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1284_1, p1308_1]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [hlam, p1308_0]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [h871, hlam, p1308_1]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [h9, hlam, p1308_0]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [h12, h865, h869, hc23, hc45, hlam, hphi, ht34, p1308_1]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [h0, h4, h7, h865, h869, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1308_1]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [h0, h4, h7, h9, hc01, hc35, hlam, hphi, ht0b, ht5b, p1308_1]
                                  · have p1308_0 := h1308c.1
                                    have p1308_1 := h1308c.2.1
                                    have p1308_2 := h1308c.2.2.1
                                    have p1308_3 := h1308c.2.2.2
                                    linarith only [hlam, p1308_0]
                        · linarith only [h1299, hlam, p1284_0]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [h1, hlam, p1284_0]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [hlam, p1284_0]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [h13, hc23, hc34, hlam, hphi, p1284_1]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [h13, hlam, p1284_0]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [h378, hlam, p1284_0]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [h4, hlam, p1284_0]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [h10, hlam, p1284_0]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [hlam, p1284_0]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [h865, hlam, p1284_0]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [h867, hlam, p1284_0]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [h7, hlam, p1284_0]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [h0, h10, h4, h7, h871, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1284_1]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [h0, h4, h7, h871, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1284_1]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [hlam, p1284_0]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [h871, hlam, p1284_1]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [h8, hlam, p1284_0]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        rcases p1284_3 (m.d 0 3) (by simp) with h1363 | h1363
                        · rcases p1284_3 (m.d 1 3) (by simp) with h1364 | h1364
                          · linarith only [h1364, hlam, p1284_0]
                          · rcases p1284_3 (m.d 2 3) (by simp) with h1366 | h1366
                            · linarith only [h1366, h867, hlam]
                            · rcases p1284_3 (m.d 3 4) (by simp) with h1368 | h1368
                              · linarith only [h1368, h871, hlam]
                              · linarith only [h13, h1368, hlam]
                        · linarith only [h1, h1363, hlam]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        rcases p1284_3 (m.d 0 3) (by simp) with h1372 | h1372
                        · rcases p1284_3 (m.d 1 3) (by simp) with h1373 | h1373
                          · linarith only [h1373, h378, hlam]
                          · linarith only [h10, h1373, hlam]
                        · linarith only [h1372, h4, hlam]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [h10, h13, hc23, hc35, hlam, hphi, p1284_1]
                      · have p1284_0 := h1284c.1
                        have p1284_1 := h1284c.2.1
                        have p1284_2 := h1284c.2.2.1
                        have p1284_3 := h1284c.2.2.2
                        linarith only [hlam, p1284_0]
              · linarith only [h12, h1277, hlam]
            · linarith only [h1276, h3, hlam]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            linarith only [h1, hlam, p1136_0]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            linarith only [h10, hlam, p1136_1]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            linarith only [hlam, p1136_0]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            linarith only [h13, hlam, p1136_1]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            linarith only [h378, hlam, p1136_1]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            linarith only [h2, hlam, p1136_0]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            linarith only [h11, hlam, p1136_1]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            linarith only [h0, h10, h4, h439, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1136_1]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            linarith only [hlam, p1136_0]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            linarith only [h439, hlam, p1136_1]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            linarith only [h3, hlam, p1136_0]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            linarith only [h12, hlam, p1136_1]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            rcases p1136_3 (m.d 0 1) (by simp) with h1393 | h1393
            · rcases p1136_3 (m.d 1 2) (by simp) with h1394 | h1394
              · rcases p1136_3 (m.d 1 3) (by simp) with h1395 | h1395
                · linarith only [h1395, h378, hlam]
                · rcases p1136_3 (m.d 1 4) (by simp) with h1397 | h1397
                  · linarith only [h1397, h439, hlam]
                  · linarith only [h13, h1397, hlam]
              · linarith only [h10, h1394, hlam]
            · linarith only [h1, h1393, hlam]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            rcases p1136_3 (m.d 0 1) (by simp) with h1402 | h1402
            · rcases p1136_3 (m.d 1 2) (by simp) with h1403 | h1403
              · rcases p1136_3 (m.d 1 3) (by simp) with h1404 | h1404
                · linarith only [h1404, h378, hlam]
                · rcases p1136_3 (m.d 1 4) (by simp) with h1406 | h1406
                  · linarith only [h1406, h439, hlam]
                  · rcases p1136_3 (m.d 1 5) (by simp) with h1408 | h1408
                    · rcases h3bigk with h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c | h1409c
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h13, h7, h871, h9, hlam, p1409_2]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h10, h13, h7, h871, h9, hlam, p1409_2]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        rcases p1409_3 (m.d 0 3) (by simp) with h1413 | h1413
                        · rcases p1409_3 (m.d 1 3) (by simp) with h1414 | h1414
                          · linarith only [h1, h1414, hlam]
                          · rcases p1409_3 (m.d 2 3) (by simp) with h1416 | h1416
                            · linarith only [h1416, h4, hlam]
                            · rcases p1409_3 (m.d 3 4) (by simp) with h1418 | h1418
                              · linarith only [h1418, hlam, p1409_0]
                              · rcases p1409_3 (m.d 3 5) (by simp) with h1420 | h1420
                                · linarith only [h1420, h8, hlam]
                                · linarith only [h1420, h871, hlam]
                        · linarith only [h1413, hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h0, h13, h378, h4, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1136_1, p1409_1]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h1, hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h12, h13, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1136_1, p1409_1]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h13, hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h378, hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h4, hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h10, hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h865, hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h867, hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h7, hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h0, h10, h4, h7, h871, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1409_1]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h0, h4, h7, h871, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1409_1]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h871, hlam, p1409_1]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h8, hlam, p1409_0]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        rcases p1409_3 (m.d 0 3) (by simp) with h1441 | h1441
                        · rcases p1409_3 (m.d 1 3) (by simp) with h1442 | h1442
                          · linarith only [h1442, hlam, p1409_0]
                          · rcases p1409_3 (m.d 2 3) (by simp) with h1444 | h1444
                            · linarith only [h1444, h867, hlam]
                            · rcases p1409_3 (m.d 3 4) (by simp) with h1446 | h1446
                              · linarith only [h1446, h871, hlam]
                              · linarith only [h13, h1446, hlam]
                        · linarith only [h1, h1441, hlam]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        rcases p1409_3 (m.d 0 3) (by simp) with h1450 | h1450
                        · rcases p1409_3 (m.d 1 3) (by simp) with h1451 | h1451
                          · linarith only [h1451, h378, hlam]
                          · linarith only [h10, h1451, hlam]
                        · linarith only [h1450, h4, hlam]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [h0, h10, h13, h4, h7, h871, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1409_1]
                      · have p1409_0 := h1409c.1
                        have p1409_1 := h1409c.2.1
                        have p1409_2 := h1409c.2.2.1
                        have p1409_3 := h1409c.2.2.2
                        linarith only [hlam, p1409_0]
                    · linarith only [h1408, h439, hlam]
              · linarith only [h11, h1403, hlam]
            · linarith only [h1402, h2, hlam]
          · have p1136_0 := h1136c.1
            have p1136_1 := h1136c.2.1
            have p1136_2 := h1136c.2.2.1
            have p1136_3 := h1136c.2.2.2
            linarith only [hlam, p1136_0]

set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x0_x0_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
    (h378 : (m.d 3 5 + m.lam ≤ m.d 1 3 ∧ m.d 3 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 4 5 (by decide) (by decide) with h439 | h439
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x0_x0_x1_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h11 h12 h13 h378 h439
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x0_x0_x1_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h11 h12 h13 h378 h439

set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
    (h13 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 5 (by decide) (by decide) with h378 | h378
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x0_x0_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h11 h12 h13 h378
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x0_x0_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h11 h12 h13 h378

set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h11 h12 h13
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h11 h12 h13

set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
    (h12 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 3 4 (by decide) (by decide) with h1461 | h1461
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1462 | h1462
    · linarith only [h10, h12, h1462, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1464 | h1464
      · linarith only [h11, h12, h1464, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1466 | h1466
        · linarith only [h0, h10, h12, h1466, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h0, h1461, h1462, h1466, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
  · rcases m.htr 1 3 5 (by decide) (by decide) with h1469 | h1469
    · linarith only [h11, h12, h1461, h1469, hlam]
    · rcases m.htr 1 4 5 (by decide) (by decide) with h1471 | h1471
      · linarith only [h11, h12, h1471, hlam]
      · rcases m.htr 2 3 4 (by decide) (by decide) with h1473 | h1473
        · linarith only [h0, h10, h12, h1461, h1473, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
        · rcases m.htr 2 3 5 (by decide) (by decide) with h1475 | h1475
          · linarith only [h10, h12, h1469, h1475, hlam]
          · rcases m.htr 2 4 5 (by decide) (by decide) with h1477 | h1477
            · linarith only [h0, h11, h12, h1475, h1477, h4, h8, hc01, hc45, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 3 4 5 (by decide) (by decide) with h1479 | h1479
              · linarith only [h11, h12, h1473, h1477, h1479, hc23, hc34, hlam, hphi]
              · rcases h1bigk with h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c | h1481c
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [hlam, p1481_0]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  rcases p1481_3 (m.d 0 1) (by simp) with h1483 | h1483
                  · rcases p1481_3 (m.d 1 2) (by simp) with h1484 | h1484
                    · linarith only [h1484, hlam, p1481_0]
                    · rcases p1481_3 (m.d 1 3) (by simp) with h1486 | h1486
                      · linarith only [h1, h1486, hlam]
                      · rcases p1481_3 (m.d 1 4) (by simp) with h1488 | h1488
                        · linarith only [h1488, h2, hlam]
                        · rcases p1481_3 (m.d 1 5) (by simp) with h1490 | h1490
                          · linarith only [h1490, h3, hlam]
                          · linarith only [h12, h1490, hlam]
                  · linarith only [h1483, hlam, p1481_0]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [h0, h1461, h1479, h4, h7, h9, hlam, p1481_2]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  rcases p1481_3 (m.d 0 1) (by simp) with h1495 | h1495
                  · rcases p1481_3 (m.d 1 2) (by simp) with h1496 | h1496
                    · linarith only [h0, h1496, hlam]
                    · linarith only [h11, h1496, hlam]
                  · linarith only [h1495, hlam, p1481_0]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  rcases p1481_3 (m.d 0 1) (by simp) with h1500 | h1500
                  · rcases p1481_3 (m.d 1 2) (by simp) with h1501 | h1501
                    · linarith only [h0, h1501, hlam]
                    · rcases p1481_3 (m.d 1 3) (by simp) with h1503 | h1503
                      · linarith only [h1, h1503, hlam]
                      · rcases p1481_3 (m.d 1 4) (by simp) with h1505 | h1505
                        · linarith only [h1505, h2, hlam]
                        · rcases p1481_3 (m.d 1 5) (by simp) with h1507 | h1507
                          · linarith only [h1507, hlam, p1481_0]
                          · rcases h3bigk with h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c | h1509c
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1461, h1479, h7, h9, hlam, p1509_2]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h11, h12, h1473, h1475, h1479, h7, h9, hlam, p1509_2]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              rcases p1509_3 (m.d 0 3) (by simp) with h1513 | h1513
                              · rcases p1509_3 (m.d 1 3) (by simp) with h1514 | h1514
                                · linarith only [h1, h1514, hlam]
                                · rcases p1509_3 (m.d 2 3) (by simp) with h1516 | h1516
                                  · linarith only [h1516, h4, hlam]
                                  · rcases p1509_3 (m.d 3 4) (by simp) with h1518 | h1518
                                    · linarith only [h1518, hlam, p1509_0]
                                    · rcases p1509_3 (m.d 3 5) (by simp) with h1520 | h1520
                                      · linarith only [h1520, h8, hlam]
                                      · linarith only [h1479, h1520, hlam]
                              · linarith only [h1513, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h0, h11, h12, h1473, h1475, h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1461, hc23, hc34, hlam, hphi, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1461, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1469, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h4, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h10, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1473, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1475, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h7, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1479, hc13, hc45, hlam, hphi, ht34, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h0, h1479, h4, h7, h9, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h1479, hlam, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h8, hlam, p1509_0]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              rcases p1509_3 (m.d 0 3) (by simp) with h1541 | h1541
                              · rcases p1509_3 (m.d 1 3) (by simp) with h1542 | h1542
                                · linarith only [h1542, hlam, p1509_0]
                                · rcases p1509_3 (m.d 2 3) (by simp) with h1544 | h1544
                                  · linarith only [h1475, h1544, hlam]
                                  · rcases p1509_3 (m.d 3 4) (by simp) with h1546 | h1546
                                    · linarith only [h1479, h1546, hlam]
                                    · linarith only [h1461, h1546, hlam]
                              · linarith only [h1, h1541, hlam]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              rcases p1509_3 (m.d 0 3) (by simp) with h1550 | h1550
                              · rcases p1509_3 (m.d 1 3) (by simp) with h1551 | h1551
                                · linarith only [h1469, h1551, hlam]
                                · linarith only [h10, h1551, hlam]
                              · linarith only [h1550, h4, hlam]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [h0, h10, h1461, h4, h8, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1509_1]
                            · have p1509_0 := h1509c.1
                              have p1509_1 := h1509c.2.1
                              have p1509_2 := h1509c.2.2.1
                              have p1509_3 := h1509c.2.2.2
                              linarith only [hlam, p1509_0]
                  · linarith only [h1500, hlam, p1481_0]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [h0, hlam, p1481_0]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [hlam, p1481_0]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [h0, h10, h12, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1481_1]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [h0, h12, h6, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b, p1481_1]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [h12, hlam, p1481_0]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [h1, hlam, p1481_0]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [h10, hlam, p1481_1]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [hlam, p1481_0]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [h1461, hlam, p1481_1]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [h1469, hlam, p1481_1]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [h2, hlam, p1481_0]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [h11, hlam, p1481_1]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [h0, h10, h11, h12, h6, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1481_1]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [hlam, p1481_0]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [h1471, hlam, p1481_1]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [h3, hlam, p1481_0]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [h10, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1481_1]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  rcases p1481_3 (m.d 0 1) (by simp) with h1575 | h1575
                  · rcases p1481_3 (m.d 1 2) (by simp) with h1576 | h1576
                    · linarith only [h12, h1576, hlam]
                    · linarith only [h10, h1576, hlam]
                  · linarith only [h1, h1575, hlam]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  rcases p1481_3 (m.d 0 1) (by simp) with h1580 | h1580
                  · rcases p1481_3 (m.d 1 2) (by simp) with h1581 | h1581
                    · linarith only [h12, h1581, hlam]
                    · linarith only [h11, h1581, hlam]
                  · linarith only [h1580, h2, hlam]
                · have p1481_0 := h1481c.1
                  have p1481_1 := h1481c.2.1
                  have p1481_2 := h1481c.2.2.1
                  have p1481_3 := h1481c.2.2.2
                  linarith only [hlam, p1481_0]

set_option maxHeartbeats 7932000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (hg5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (hg6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (hg7 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg8 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (hg9 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h10 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
    (h11 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5 := hg5
  have h6 := hg6
  have h7 := hg7
  have h8 := hg8
  have h9 := hg9
  rcases m.htr 1 2 5 (by decide) (by decide) with h12 | h12
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x0_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h11 h12
  · exact r1l7_11_13_25_L_I_L_I_H_I_s9_x0_x0_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 h10 h11 h12

end R2N4
