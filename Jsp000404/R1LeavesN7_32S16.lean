import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_32S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7264000 in
set_option maxHeartbeats 7264000 in
theorem r1l7_22_13_15_M_IR_L_I_L_I_s0 (m : N7Model)
    (hb2 : CMSig2_7_M_IR m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h2ehi := hb2.2.1
  have h2bigk := hb2.2.2.2
  have h3bigk := hb3.1
  have h3emax := hb3.2.2
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h879 | h879
  · rcases m.htr 0 1 5 (by decide) (by decide) with h880 | h880
    · rcases m.htr 0 2 3 (by decide) (by decide) with h881 | h881
      · rcases m.htr 0 2 4 (by decide) (by decide) with h882 | h882
        · rcases m.htr 0 2 5 (by decide) (by decide) with h883 | h883
          · rcases m.htr 0 3 4 (by decide) (by decide) with h884 | h884
            · rcases m.htr 0 3 5 (by decide) (by decide) with h885 | h885
              · rcases m.htr 0 4 5 (by decide) (by decide) with h886 | h886
                · rcases m.htr 1 2 3 (by decide) (by decide) with h887 | h887
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h888 | h888
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h889 | h889
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h890 | h890
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h891 | h891
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h892 | h892
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h893 | h893
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h894 | h894
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h895 | h895
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h896 | h896
                                    · linarith only [h0, h879, h887, h893, h896, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                    · linarith only [h0, h879, h890, h892, h896, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h0, h879, h890, h892, h895, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h879, h885, h894, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h0, h879, h884, h893, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h0, h879, h884, h886, h888, h892, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h0, h879, h885, h890, h891, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h879, h884, h887, h890, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h879, h887, h889, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h879, h883, h884, h886, h888, hc24, hlam, hphi, u2ehi4]
                  · linarith only [h0, h879, h881, h887, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h908 | h908
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h909 | h909
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h910 | h910
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h911 | h911
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h912 | h912
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h913 | h913
                            · linarith only [h0, h879, h882, h886, h911, h913, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h915 | h915
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h916 | h916
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h917 | h917
                                  · linarith only [h882, h886, h917, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h919 | h919
                                    · linarith only [h0, h879, h886, h908, h915, h919, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · rcases h2bigk with h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c | h921c
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        linarith only [hlam, p921_0]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        linarith only [h0, hlam, p921_0]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        rcases p921_3 (m.d 0 2) (by simp) with h924 | h924
                                        · rcases p921_3 (m.d 1 2) (by simp) with h925 | h925
                                          · rcases p921_3 (m.d 2 3) (by simp) with h926 | h926
                                            · linarith only [h926, hlam, p921_0]
                                            · rcases p921_3 (m.d 2 4) (by simp) with h928 | h928
                                              · linarith only [h882, h928, hlam]
                                              · rcases p921_3 (m.d 2 5) (by simp) with h930 | h930
                                                · linarith only [h883, h930, hlam]
                                                · rcases h3bigk with h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c | h932c
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [hlam, p932_0]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [h0, h879, h908, h916, h919, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p932_1]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [h0, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p932_1, u2ehi2]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    rcases p932_3 (m.d 0 3) (by simp) with h936 | h936
                                                    · rcases p932_3 (m.d 1 3) (by simp) with h937 | h937
                                                      · linarith only [h879, h937, hlam]
                                                      · linarith only [h911, h937, hlam]
                                                    · linarith only [h936, hlam, p932_0]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    rcases p932_3 (m.d 0 3) (by simp) with h941 | h941
                                                    · rcases p932_3 (m.d 1 3) (by simp) with h942 | h942
                                                      · linarith only [h879, h942, hlam]
                                                      · linarith only [h912, h942, hlam]
                                                    · linarith only [h941, hlam, p932_0]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [h879, hlam, p932_0]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [hlam, p932_0]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [h0, h879, h916, h917, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p932_1, u2ehi3]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [h0, h879, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p932_1]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [h0, h879, h919, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p932_1]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [h881, hlam, p932_1]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [h908, hlam, p932_1]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [hlam, p932_0]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [h0, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p921_1, p932_1]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [h0, h919, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p921_1, p932_1]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [h884, hlam, p932_0]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [h911, hlam, p932_0]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [h915, hlam, p932_0]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [hlam, p932_0]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [h919, hlam, p932_0]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [h885, hlam, p932_0]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [h912, hlam, p932_0]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [h916, hlam, p932_0]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [h0, h879, h885, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p932_1]
                                                  · have p932_0 := h932c.1
                                                    have p932_1 := h932c.2.1
                                                    have p932_2 := h932c.2.2.1
                                                    have p932_3 := h932c.2.2.2
                                                    linarith only [hlam, p932_0]
                                          · linarith only [h908, h925, hlam]
                                        · linarith only [h924, hlam, p921_0]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        rcases p921_3 (m.d 0 2) (by simp) with h968 | h968
                                        · rcases p921_3 (m.d 1 2) (by simp) with h969 | h969
                                          · rcases p921_3 (m.d 2 3) (by simp) with h970 | h970
                                            · linarith only [h881, h970, hlam]
                                            · linarith only [h915, h970, hlam]
                                          · linarith only [h909, h969, hlam]
                                        · linarith only [h968, hlam, p921_0]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        rcases p921_3 (m.d 0 2) (by simp) with h975 | h975
                                        · rcases p921_3 (m.d 1 2) (by simp) with h976 | h976
                                          · rcases p921_3 (m.d 2 3) (by simp) with h977 | h977
                                            · linarith only [h881, h977, hlam]
                                            · linarith only [h916, h977, hlam]
                                          · linarith only [h910, h976, hlam]
                                        · linarith only [h975, hlam, p921_0]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        linarith only [h0, h880, h910, h917, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p921_1, u2ehi3]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        linarith only [hlam, p921_0]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        rcases p921_3 (m.d 0 2) (by simp) with h984 | h984
                                        · linarith only [h0, h984, hlam]
                                        · linarith only [h881, h984, hlam]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        rcases p921_3 (m.d 0 2) (by simp) with h987 | h987
                                        · linarith only [h0, h987, hlam]
                                        · linarith only [h882, h987, hlam]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        rcases p921_3 (m.d 0 2) (by simp) with h990 | h990
                                        · linarith only [h0, h990, hlam]
                                        · linarith only [h883, h990, hlam]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        linarith only [h881, hlam, p921_0]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        linarith only [h908, hlam, p921_0]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        linarith only [hlam, p921_0]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        linarith only [hc23, hlam, hphi, p921_1, u2ehi3]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        linarith only [h879, h908, h917, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p921_1, u2ehi3]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        linarith only [h882, hlam, p921_0]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        linarith only [h909, hlam, p921_0]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        linarith only [h915, hlam, p921_0]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        linarith only [hlam, p921_0]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        linarith only [h917, hlam, p921_0]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        linarith only [h883, hlam, p921_0]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        linarith only [h910, hlam, p921_0]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        linarith only [h916, hlam, p921_0]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        linarith only [hc25, hlam, hphi, p921_1, u2ehi3]
                                      · have p921_0 := h921c.1
                                        have p921_1 := h921c.2.1
                                        have p921_2 := h921c.2.2.1
                                        have p921_3 := h921c.2.2.2
                                        linarith only [hlam, p921_0]
                                · linarith only [h0, h879, h885, h916, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                              · linarith only [h0, h879, h884, h915, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · linarith only [h0, h879, h885, h911, h912, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h879, h884, h908, h911, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                      · linarith only [h0, h879, h908, h910, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h879, h882, h885, h886, h908, h909, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h879, h883, h885, h908, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1015 | h1015
                · linarith only [h1015, h884, h885, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1017 | h1017
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1018 | h1018
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1019 | h1019
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1020 | h1020
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1021 | h1021
                          · linarith only [h0, h1021, h879, h885, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1023 | h1023
                            · linarith only [h0, h1015, h1020, h1021, h1023, h880, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1025 | h1025
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1026 | h1026
                                · linarith only [h1018, h1020, h1026, h879, h885, hc23, hlam, hphi, u2ehi3]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1028 | h1028
                                  · linarith only [h1015, h1028, h882, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1030 | h1030
                                    · linarith only [h1015, h1017, h1021, h1025, h1030, h880, h882, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                    · rcases h2bigk with h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c | h1032c
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        linarith only [hlam, p1032_0]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        linarith only [h0, hlam, p1032_0]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        rcases p1032_3 (m.d 0 2) (by simp) with h1035 | h1035
                                        · rcases p1032_3 (m.d 1 2) (by simp) with h1036 | h1036
                                          · rcases p1032_3 (m.d 2 3) (by simp) with h1037 | h1037
                                            · linarith only [h1037, hlam, p1032_0]
                                            · rcases p1032_3 (m.d 2 4) (by simp) with h1039 | h1039
                                              · linarith only [h1039, h882, hlam]
                                              · rcases p1032_3 (m.d 2 5) (by simp) with h1041 | h1041
                                                · linarith only [h1041, h883, hlam]
                                                · linarith only [h1026, h1041, hlam]
                                          · linarith only [h1017, h1036, hlam]
                                        · linarith only [h1035, hlam, p1032_0]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        rcases p1032_3 (m.d 0 2) (by simp) with h1046 | h1046
                                        · rcases p1032_3 (m.d 1 2) (by simp) with h1047 | h1047
                                          · rcases p1032_3 (m.d 2 3) (by simp) with h1048 | h1048
                                            · linarith only [h1048, h881, hlam]
                                            · linarith only [h1025, h1048, hlam]
                                          · linarith only [h1018, h1047, hlam]
                                        · linarith only [h1046, hlam, p1032_0]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        rcases p1032_3 (m.d 0 2) (by simp) with h1053 | h1053
                                        · rcases p1032_3 (m.d 1 2) (by simp) with h1054 | h1054
                                          · rcases p1032_3 (m.d 2 3) (by simp) with h1055 | h1055
                                            · linarith only [h1055, h881, hlam]
                                            · rcases p1032_3 (m.d 2 4) (by simp) with h1057 | h1057
                                              · linarith only [h1057, h882, hlam]
                                              · rcases p1032_3 (m.d 2 5) (by simp) with h1059 | h1059
                                                · linarith only [h1059, hlam, p1032_0]
                                                · rcases h3bigk with h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c | h1061c
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [hlam, p1061_0]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [h885, hc13, hc35, hlam, hphi, p1061_1]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [h1030, h885, hc45, hlam, hphi, ht23, ht34, p1061_1, u2ehi2]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [h1030, h885, hc34, hc45, hlam, hphi, p1061_1]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [h885, hlam, p1061_0]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [h879, hlam, p1061_0]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [hlam, p1061_0]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [h1021, h880, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1061_1, u2ehi2]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [h0, h1021, h880, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1061_1]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [h1021, hlam, p1061_0]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [h881, hlam, p1061_1]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [h1017, hlam, p1061_1]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [hlam, p1061_0]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [h1030, h881, h885, hc34, hc45, hlam, hphi, p1061_1]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [h1026, hlam, p1061_0]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [h884, hlam, p1061_0]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [h1020, hlam, p1061_0]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [h1025, hlam, p1061_0]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [hlam, p1061_0]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [h1030, hlam, p1061_0]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [h1030, h881, hc45, hlam, hphi, ht23, ht34, p1061_1, u2ehi2]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [h1018, h1020, h1030, hc45, hlam, hphi, ht23, ht34, p1061_1, u2ehi3]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [h1025, h1030, hc45, hlam, hphi, ht23, ht34, p1061_1, u2ehi3]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    rcases p1061_3 (m.d 0 3) (by simp) with h1085 | h1085
                                                    · linarith only [h1085, h885, hlam]
                                                    · linarith only [h1085, h884, hlam]
                                                  · have p1061_0 := h1061c.1
                                                    have p1061_1 := h1061c.2.1
                                                    have p1061_2 := h1061c.2.2.1
                                                    have p1061_3 := h1061c.2.2.2
                                                    linarith only [hlam, p1061_0]
                                          · linarith only [h1019, h1054, hlam]
                                        · linarith only [h1053, hlam, p1032_0]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        linarith only [h0, h1018, h1020, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi3]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        linarith only [hlam, p1032_0]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        rcases p1032_3 (m.d 0 2) (by simp) with h1093 | h1093
                                        · linarith only [h0, h1093, hlam]
                                        · linarith only [h1093, h881, hlam]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        rcases p1032_3 (m.d 0 2) (by simp) with h1096 | h1096
                                        · linarith only [h0, h1096, hlam]
                                        · linarith only [h1096, h882, hlam]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        rcases p1032_3 (m.d 0 2) (by simp) with h1099 | h1099
                                        · linarith only [h0, h1099, hlam]
                                        · linarith only [h1099, h883, hlam]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        linarith only [h881, hlam, p1032_0]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        linarith only [h1017, hlam, p1032_0]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        linarith only [hlam, p1032_0]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        linarith only [h1019, h1026, h880, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi3]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        linarith only [h1026, hlam, p1032_1]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        linarith only [h882, hlam, p1032_0]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        linarith only [h1018, hlam, p1032_0]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        linarith only [h1025, hlam, p1032_0]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        linarith only [hlam, p1032_0]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        linarith only [h1028, hlam, p1032_0]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        linarith only [h883, hlam, p1032_0]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        linarith only [h1019, hlam, p1032_0]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        linarith only [h0, h1019, h880, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi2]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        linarith only [h0, h1019, h880, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1032_1, u2ehi3]
                                      · have p1032_0 := h1032c.1
                                        have p1032_1 := h1032c.2.1
                                        have p1032_2 := h1032c.2.2.1
                                        have p1032_3 := h1032c.2.2.2
                                        linarith only [hlam, p1032_0]
                              · linarith only [h0, h1025, h879, h884, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h1020, h884, h885, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h1017, h1019, h879, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h1017, h1018, h879, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1017, h879, h881, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1122 | h1122
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1123 | h1123
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1124 | h1124
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1125 | h1125
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1126 | h1126
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1127 | h1127
                        · linarith only [h0, h1127, h879, h882, h884, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1129 | h1129
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1130 | h1130
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1131 | h1131
                              · linarith only [h1122, h1126, h1131, h880, h884, hc23, hlam, hphi, u2ehi4]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1133 | h1133
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1134 | h1134
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1135 | h1135
                                    · rcases h2bigk with h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c | h1136c
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        linarith only [hlam, p1136_0]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        linarith only [h0, hlam, p1136_0]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        rcases p1136_3 (m.d 0 2) (by simp) with h1139 | h1139
                                        · rcases p1136_3 (m.d 1 2) (by simp) with h1140 | h1140
                                          · rcases p1136_3 (m.d 2 3) (by simp) with h1141 | h1141
                                            · linarith only [h1141, hlam, p1136_0]
                                            · rcases p1136_3 (m.d 2 4) (by simp) with h1143 | h1143
                                              · linarith only [h1143, h882, hlam]
                                              · linarith only [h1131, h1143, hlam]
                                          · linarith only [h1124, h1140, hlam]
                                        · linarith only [h1139, hlam, p1136_0]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        rcases p1136_3 (m.d 0 2) (by simp) with h1148 | h1148
                                        · rcases p1136_3 (m.d 1 2) (by simp) with h1149 | h1149
                                          · rcases p1136_3 (m.d 2 3) (by simp) with h1150 | h1150
                                            · linarith only [h1150, h881, hlam]
                                            · rcases p1136_3 (m.d 2 4) (by simp) with h1152 | h1152
                                              · linarith only [h1152, hlam, p1136_0]
                                              · rcases p1136_3 (m.d 2 5) (by simp) with h1154 | h1154
                                                · linarith only [h1154, h883, hlam]
                                                · rcases h3bigk with h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c | h1156c
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [hlam, p1156_0]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [h1124, h884, hc23, hc34, hlam, hphi, p1156_1]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [h884, hc34, hlam, hphi, ht23, p1156_1, u2ehi2]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [h884, hlam, p1156_0]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    rcases p1156_3 (m.d 0 3) (by simp) with h1161 | h1161
                                                    · rcases p1156_3 (m.d 1 3) (by simp) with h1162 | h1162
                                                      · linarith only [h1162, h879, hlam]
                                                      · linarith only [h1129, h1162, hlam]
                                                    · linarith only [h1161, hlam, p1156_0]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [h879, hlam, p1156_0]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [hlam, p1156_0]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [h0, h1133, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1156_1, u2ehi4]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [h1127, hlam, p1156_0]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [h0, h1135, h879, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1156_1]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [h881, hlam, p1156_1]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [h1124, hlam, p1156_1]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [hlam, p1156_0]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [h1131, hlam, p1156_0]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [h1131, h1135, hc02, hc45, hlam, hphi, ht0b, ht5b, p1136_1, p1156_1]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [h881, hc34, hlam, hphi, ht23, p1156_1, u2ehi2]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [h1126, h1129, hc34, hlam, hphi, ht23, p1156_1, u2ehi4]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [hc34, hlam, hphi, ht23, p1156_1, u2ehi2]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [hlam, p1156_0]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    rcases p1156_3 (m.d 0 3) (by simp) with h1180 | h1180
                                                    · linarith only [h1180, h884, hlam]
                                                    · linarith only [h1122, h1180, hlam]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [h1122, hlam, p1156_0]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [h1129, hlam, p1156_0]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [h1133, hlam, p1156_0]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [h1135, hlam, p1156_1]
                                                  · have p1156_0 := h1156c.1
                                                    have p1156_1 := h1156c.2.1
                                                    have p1156_2 := h1156c.2.2.1
                                                    have p1156_3 := h1156c.2.2.2
                                                    linarith only [hlam, p1156_0]
                                          · linarith only [h1125, h1149, hlam]
                                        · linarith only [h1148, hlam, p1136_0]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        rcases p1136_3 (m.d 0 2) (by simp) with h1190 | h1190
                                        · rcases p1136_3 (m.d 1 2) (by simp) with h1191 | h1191
                                          · rcases p1136_3 (m.d 2 3) (by simp) with h1192 | h1192
                                            · linarith only [h1192, h881, hlam]
                                            · linarith only [h1133, h1192, hlam]
                                          · linarith only [h1126, h1191, hlam]
                                        · linarith only [h1190, hlam, p1136_0]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        linarith only [h0, h1126, h1129, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1136_1, u2ehi4]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        linarith only [hlam, p1136_0]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        rcases p1136_3 (m.d 0 2) (by simp) with h1199 | h1199
                                        · linarith only [h0, h1199, hlam]
                                        · linarith only [h1199, h881, hlam]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        rcases p1136_3 (m.d 0 2) (by simp) with h1202 | h1202
                                        · linarith only [h0, h1202, hlam]
                                        · linarith only [h1202, h882, hlam]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        rcases p1136_3 (m.d 0 2) (by simp) with h1205 | h1205
                                        · linarith only [h0, h1205, hlam]
                                        · linarith only [h1205, h883, hlam]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        linarith only [h881, hlam, p1136_0]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        linarith only [h1124, hlam, p1136_0]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        linarith only [hlam, p1136_0]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        linarith only [h1131, hlam, p1136_1]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        linarith only [hc23, hlam, hphi, p1136_1, u2ehi4]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        linarith only [h882, hlam, p1136_0]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        linarith only [h1125, hlam, p1136_0]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        linarith only [hc24, hlam, hphi, p1136_1, u2ehi2]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        linarith only [hlam, p1136_0]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        linarith only [h0, h882, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1136_1, u2ehi4]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        linarith only [h883, hlam, p1136_0]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        linarith only [h1126, hlam, p1136_0]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        linarith only [h1133, hlam, p1136_0]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        linarith only [h1134, hlam, p1136_1]
                                      · have p1136_0 := h1136c.1
                                        have p1136_1 := h1136c.2.1
                                        have p1136_2 := h1136c.2.2.1
                                        have p1136_3 := h1136c.2.2.2
                                        linarith only [hlam, p1136_0]
                                    · linarith only [h1126, h1129, h1135, h879, h884, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                                  · linarith only [h0, h1129, h1130, h1134, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h1122, h1133, h884, hc23, hc34, hlam, hphi]
                            · linarith only [h1122, h1123, h1124, h1127, h1130, h884, hc34, hlam, hphi, ht23, u2ehi2]
                          · linarith only [h1122, h1124, h1129, h884, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h0, h1124, h1126, h879, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h1124, h1125, h879, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1124, h882, hc23, hlam, hphi, u2ehi3]
                · linarith only [h1122, h1123, h884, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1232 | h1232
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1233 | h1233
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1234 | h1234
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1235 | h1235
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1236 | h1236
                        · linarith only [h0, h1236, h879, h884, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1238 | h1238
                          · linarith only [h1122, h1238, h879, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1240 | h1240
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1241 | h1241
                              · linarith only [h1232, h1233, h1238, h1241, h880, h884, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1243 | h1243
                                · linarith only [h1122, h1233, h1243, h879, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1245 | h1245
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1246 | h1246
                                    · rcases h2bigk with h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c | h1247c
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        linarith only [hlam, p1247_0]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        linarith only [h0, hlam, p1247_0]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        rcases p1247_3 (m.d 0 2) (by simp) with h1250 | h1250
                                        · rcases p1247_3 (m.d 1 2) (by simp) with h1251 | h1251
                                          · rcases p1247_3 (m.d 2 3) (by simp) with h1252 | h1252
                                            · linarith only [h1252, hlam, p1247_0]
                                            · rcases p1247_3 (m.d 2 4) (by simp) with h1254 | h1254
                                              · linarith only [h1254, h882, hlam]
                                              · linarith only [h1241, h1254, hlam]
                                          · linarith only [h1233, h1251, hlam]
                                        · linarith only [h1250, hlam, p1247_0]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        rcases p1247_3 (m.d 0 2) (by simp) with h1259 | h1259
                                        · rcases p1247_3 (m.d 1 2) (by simp) with h1260 | h1260
                                          · rcases p1247_3 (m.d 2 3) (by simp) with h1261 | h1261
                                            · linarith only [h1261, h881, hlam]
                                            · rcases p1247_3 (m.d 2 4) (by simp) with h1263 | h1263
                                              · linarith only [h1263, hlam, p1247_0]
                                              · rcases p1247_3 (m.d 2 5) (by simp) with h1265 | h1265
                                                · linarith only [h1265, h883, hlam]
                                                · rcases h3bigk with h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [hlam, p1267_0]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [h1122, h1246, hc13, hc34, hlam, hphi, p1267_1]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [h1122, h1246, hc34, hlam, hphi, ht23, p1267_1, u2ehi2]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [h884, hlam, p1267_0]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [h1122, hlam, p1267_0]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [h879, hlam, p1267_0]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [hlam, p1267_0]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [h0, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1267_1, u2ehi2]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [h1236, hlam, p1267_0]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [h1238, hlam, p1267_0]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [h881, hlam, p1267_1]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [h1233, hlam, p1267_1]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [hlam, p1267_0]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [h1241, hlam, p1267_0]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [h1243, hlam, p1267_0]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [h881, hc34, hlam, hphi, ht23, p1267_1, u2ehi2]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [h1233, hc34, hlam, hphi, ht23, p1267_1, u2ehi2]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [hc34, hlam, hphi, ht23, p1267_1, u2ehi2]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [hlam, p1267_0]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [h1122, h1233, h879, hc34, hlam, hphi, ht23, p1267_1, u2ehi2]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [h1233, h879, hc35, hlam, hphi, ht23, p1267_1, u2ehi2]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [h1233, hc35, hlam, hphi, ht23, p1267_1, u2ehi2]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [hc35, hlam, hphi, ht23, p1267_1, u2ehi2]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [h1246, hlam, p1267_1]
                                                  · have p1267_0 := h1267c.1
                                                    have p1267_1 := h1267c.2.1
                                                    have p1267_2 := h1267c.2.2.1
                                                    have p1267_3 := h1267c.2.2.2
                                                    linarith only [hlam, p1267_0]
                                          · linarith only [h1234, h1260, hlam]
                                        · linarith only [h1259, hlam, p1247_0]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        rcases p1247_3 (m.d 0 2) (by simp) with h1295 | h1295
                                        · rcases p1247_3 (m.d 1 2) (by simp) with h1296 | h1296
                                          · rcases p1247_3 (m.d 2 3) (by simp) with h1297 | h1297
                                            · linarith only [h1297, h881, hlam]
                                            · rcases p1247_3 (m.d 2 4) (by simp) with h1299 | h1299
                                              · linarith only [h1299, h882, hlam]
                                              · linarith only [h1245, h1299, hlam]
                                          · linarith only [h1235, h1296, hlam]
                                        · linarith only [h1295, hlam, p1247_0]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        linarith only [h0, h1233, h879, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1247_1, u2ehi2]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        linarith only [hlam, p1247_0]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        rcases p1247_3 (m.d 0 2) (by simp) with h1306 | h1306
                                        · linarith only [h0, h1306, hlam]
                                        · linarith only [h1306, h881, hlam]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        rcases p1247_3 (m.d 0 2) (by simp) with h1309 | h1309
                                        · linarith only [h0, h1309, hlam]
                                        · linarith only [h1309, h882, hlam]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        rcases p1247_3 (m.d 0 2) (by simp) with h1312 | h1312
                                        · linarith only [h0, h1312, hlam]
                                        · linarith only [h1312, h883, hlam]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        linarith only [h881, hlam, p1247_0]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        linarith only [h1233, hlam, p1247_0]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        linarith only [hlam, p1247_0]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        linarith only [h1241, hlam, p1247_1]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        linarith only [h1243, hlam, p1247_1]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        linarith only [h882, hlam, p1247_0]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        linarith only [h1234, hlam, p1247_0]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        linarith only [hc24, hlam, hphi, p1247_1, u2ehi2]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        linarith only [hlam, p1247_0]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        linarith only [h0, h1243, h882, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1247_1, u2ehi2]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        linarith only [h883, hlam, p1247_0]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        linarith only [h1235, hlam, p1247_0]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        linarith only [hc25, hlam, hphi, p1247_1, u2ehi2]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        linarith only [h1245, hlam, p1247_1]
                                      · have p1247_0 := h1247c.1
                                        have p1247_1 := h1247c.2.1
                                        have p1247_2 := h1247c.2.2.1
                                        have p1247_3 := h1247c.2.2.2
                                        linarith only [hlam, p1247_0]
                                    · linarith only [h0, h1233, h1235, h1245, h1246, h879, h880, h884, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                  · linarith only [h1232, h1245, h884, hc34, hlam, hphi, ht23, u2ehi3]
                            · linarith only [h1232, h1233, h1236, h1240, h884, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h0, h1233, h1235, h879, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h1233, h1234, h879, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1233, h882, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1336 | h1336
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1337 | h1337
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1338 | h1338
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1339 | h1339
                        · linarith only [h1339, h879, h884, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1341 | h1341
                          · linarith only [h1122, h1341, h879, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1343 | h1343
                            · linarith only [h1232, h1336, h1339, h1343, h879, h884, hc34, hlam, hphi, ht23, u2ehi2]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1345 | h1345
                              · linarith only [h1336, h1345, h879, h884, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1347 | h1347
                                · linarith only [h1122, h1336, h1347, h879, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1349 | h1349
                                  · linarith only [h1232, h1336, h1349, h879, h884, hc24, hlam, hphi, u2ehi2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1351 | h1351
                                    · linarith only [h1232, h1336, h1351, h879, h884, hc34, hlam, hphi, ht23, u2ehi2]
                                    · linarith only [h1336, h1351, h879, h884, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h1336, h1338, h879, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h1336, h1337, h879, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1232, h1336, h880, h882, hc23, hlam, hphi, u2ehi3]
          · linarith only [h881, h883, hc25, hlam, hphi, u2ehi2]
        · linarith only [h881, h882, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h879, h881, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1360 | h1360
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1361 | h1361
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1362 | h1362
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1363 | h1363
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1364 | h1364
              · linarith only [h1364, h879, h880, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1366 | h1366
                · linarith only [h1363, h1366, h879, h880, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1368 | h1368
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1369 | h1369
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1370 | h1370
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1371 | h1371
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1372 | h1372
                          · linarith only [h1364, h1370, h1372, h879, h880, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h1369, h1371, h1372, h879, h880, hc35, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h1363, h1364, h1371, hc13, hc35, hlam, hphi]
                      · linarith only [h0, h1362, h1370, hlam]
                    · linarith only [h0, h1362, h1369, hc24, hlam, hphi, u2ehi4]
                  · linarith only [h0, h1361, h1368, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1379 | h1379
              · linarith only [h1379, h879, h880, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1381 | h1381
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1382 | h1382
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1383 | h1383
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1384 | h1384
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1385 | h1385
                        · linarith only [h1363, h1381, h1385, h879, h880, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1387 | h1387
                          · linarith only [h1379, h1387, h879, h880, hlam]
                          · linarith only [h1382, h1387, h879, h880, hc35, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h0, h1382, h1384, h879, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h1382, h1383, h879, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1361, h1382, hc23, hlam, hphi, u2ehi3]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1393 | h1393
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1394 | h1394
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1395 | h1395
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1396 | h1396
                        · linarith only [h1363, h1396, h879, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1398 | h1398
                          · linarith only [h1379, h1398, h879, hlam]
                          · linarith only [h1393, h1398, h879, h880, hc35, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h0, h1362, h1393, h1395, h879, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h1393, h1394, h879, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h1360, h1393, h879, hlam]
          · linarith only [h1360, h1362, hc25, hlam, hphi, u2ehi2]
        · linarith only [h1360, h1361, hc24, hlam, hphi, u2ehi2]
      · linarith only [h0, h1360, h879, hlam]
  · exact r1l7_22_13_15_M_IR_L_I_L_I_s1 m hb2 hb3 hb5 h0 h879

end R2N4
