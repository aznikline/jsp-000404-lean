import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_62S10

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3222000 in
set_option maxHeartbeats 3222000 in
theorem r1l7_22_13_15_M_LI_L_0_L_I_x1 (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h859 | h859
  · rcases m.htr 0 1 5 (by decide) (by decide) with h860 | h860
    · rcases m.htr 0 2 3 (by decide) (by decide) with h861 | h861
      · rcases m.htr 0 2 4 (by decide) (by decide) with h862 | h862
        · rcases m.htr 0 2 5 (by decide) (by decide) with h863 | h863
          · rcases m.htr 0 3 5 (by decide) (by decide) with h864 | h864
            · rcases m.htr 0 4 5 (by decide) (by decide) with h865 | h865
              · rcases m.htr 1 2 3 (by decide) (by decide) with h866 | h866
                · rcases m.htr 1 2 4 (by decide) (by decide) with h867 | h867
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h868 | h868
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h869 | h869
                      · linarith only [h0, h859, h869, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h864, h866, h869, hc23, hlam, hphi, u3elo0]
                    · linarith only [h0, h859, h866, h868, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · linarith only [h0, h859, h862, h867, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h859, h866, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h875 | h875
                · rcases m.htr 1 2 4 (by decide) (by decide) with h876 | h876
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h877 | h877
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h878 | h878
                      · linarith only [h0, h859, h878, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h0, h859, h864, h875, h878, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h877, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h859, h862, h864, h865, h876, hlam]
                · linarith only [h0, h875, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h884 | h884
              · rcases m.htr 1 2 3 (by decide) (by decide) with h885 | h885
                · rcases m.htr 1 2 4 (by decide) (by decide) with h886 | h886
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h887 | h887
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h888 | h888
                      · linarith only [h0, h859, h864, h888, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h890 | h890
                        · linarith only [h0, h860, h885, h888, h890, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h892 | h892
                          · linarith only [h859, h864, h885, h892, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h894 | h894
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h895 | h895
                              · rcases h2bigk with h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [hlam, p896_0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h0, hlam, p896_0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  rcases p896_3 (m.d 0 2) (by simp) with h899 | h899
                                  · rcases p896_3 (m.d 1 2) (by simp) with h900 | h900
                                    · rcases p896_3 (m.d 2 3) (by simp) with h901 | h901
                                      · linarith only [h901, hlam, p896_0]
                                      · rcases p896_3 (m.d 2 4) (by simp) with h903 | h903
                                        · linarith only [h862, h903, hlam]
                                        · linarith only [h890, h903, hlam]
                                    · linarith only [h885, h900, hlam]
                                  · linarith only [h899, hlam, p896_0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h0, h894, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p896_1, u2elo1]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  rcases p896_3 (m.d 0 2) (by simp) with h909 | h909
                                  · rcases p896_3 (m.d 1 2) (by simp) with h910 | h910
                                    · rcases p896_3 (m.d 2 3) (by simp) with h911 | h911
                                      · linarith only [h861, h911, hlam]
                                      · rcases p896_3 (m.d 2 4) (by simp) with h913 | h913
                                        · linarith only [h862, h913, hlam]
                                        · linarith only [h894, h913, hlam]
                                    · linarith only [h887, h910, hlam]
                                  · linarith only [h909, hlam, p896_0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [hc02, hlam, hphi, p896_1, u2elo1]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [hlam, p896_0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  rcases p896_3 (m.d 0 2) (by simp) with h920 | h920
                                  · linarith only [h0, h920, hlam]
                                  · linarith only [h861, h920, hlam]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h894, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p896_1, u2elo1]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  rcases p896_3 (m.d 0 2) (by simp) with h924 | h924
                                  · linarith only [h0, h924, hlam]
                                  · linarith only [h863, h924, hlam]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h861, hlam, p896_0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h885, hlam, p896_0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [hlam, p896_0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h890, hlam, p896_1]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h892, hlam, p896_1]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h862, hlam, p896_0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h886, hlam, p896_0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h862, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p896_1, u2elo0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [hlam, p896_0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h0, h862, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p896_1, u2elo1]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h863, hlam, p896_0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h887, hlam, p896_0]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h0, h863, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p896_1, u2elo1]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [h894, hlam, p896_1]
                                · have p896_0 := h896c.1
                                  have p896_1 := h896c.2.1
                                  have p896_2 := h896c.2.2.1
                                  have p896_3 := h896c.2.2.2
                                  linarith only [hlam, p896_0]
                              · linarith only [h0, h862, h884, h890, h895, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h943 | h943
                              · linarith only [h890, h894, h943, hc23, hlam, hphi, u3elo3]
                              · linarith only [h0, h862, h884, h890, h943, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h887, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h859, h885, h886, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h885, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h949 | h949
                · rcases m.htr 1 2 4 (by decide) (by decide) with h950 | h950
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h951 | h951
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h952 | h952
                      · linarith only [h0, h859, h952, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h954 | h954
                        · linarith only [h0, h860, h949, h952, h954, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h956 | h956
                          · linarith only [h0, h860, h864, h949, h952, h956, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h958 | h958
                            · linarith only [h862, h884, h958, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h960 | h960
                              · linarith only [h862, h884, h954, h960, hc23, hlam, hphi, u3elo3]
                              · rcases h2bigk with h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c | h962c
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  linarith only [hlam, p962_0]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  linarith only [h0, hlam, p962_0]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  rcases p962_3 (m.d 0 2) (by simp) with h965 | h965
                                  · rcases p962_3 (m.d 1 2) (by simp) with h966 | h966
                                    · rcases p962_3 (m.d 2 3) (by simp) with h967 | h967
                                      · linarith only [h967, hlam, p962_0]
                                      · rcases p962_3 (m.d 2 4) (by simp) with h969 | h969
                                        · linarith only [h862, h969, hlam]
                                        · linarith only [h954, h969, hlam]
                                    · linarith only [h949, h966, hlam]
                                  · linarith only [h965, hlam, p962_0]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  rcases p962_3 (m.d 0 2) (by simp) with h974 | h974
                                  · rcases p962_3 (m.d 1 2) (by simp) with h975 | h975
                                    · rcases p962_3 (m.d 2 3) (by simp) with h976 | h976
                                      · linarith only [h861, h976, hlam]
                                      · rcases p962_3 (m.d 2 4) (by simp) with h978 | h978
                                        · linarith only [h978, hlam, p962_0]
                                        · rcases p962_3 (m.d 2 5) (by simp) with h980 | h980
                                          · linarith only [h863, h980, hlam]
                                          · linarith only [h958, h980, hlam]
                                    · linarith only [h950, h975, hlam]
                                  · linarith only [h974, hlam, p962_0]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  rcases p962_3 (m.d 0 2) (by simp) with h985 | h985
                                  · rcases p962_3 (m.d 1 2) (by simp) with h986 | h986
                                    · rcases p962_3 (m.d 2 3) (by simp) with h987 | h987
                                      · linarith only [h861, h987, hlam]
                                      · rcases p962_3 (m.d 2 4) (by simp) with h989 | h989
                                        · linarith only [h862, h989, hlam]
                                        · rcases p962_3 (m.d 2 5) (by simp) with h991 | h991
                                          · linarith only [h991, hlam, p962_0]
                                          · rcases h5bigk with h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [hlam, p993_0]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [h0, h860, h951, h954, h958, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p993_1, u2elo1]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [h0, h860, h954, h958, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p993_1, u2elo1]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [h864, hlam, p993_0]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [h884, hlam, p993_0]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [h860, hlam, p993_0]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [hlam, p993_0]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [h0, h860, h954, h958, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p993_1, u2elo1]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [h952, hlam, p993_0]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [h0, h860, h954, h960, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p993_1, u2elo1]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [h863, hlam, p993_1]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [h951, hlam, p993_1]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [hlam, p993_0]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [h956, hlam, p993_1]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [h958, hlam, p993_0]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [h860, h952, hc13, hlam, hphi, p993_1, u3elo4]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [h951, h954, h958, hc23, hlam, hphi, p993_1, u3elo4]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [h954, h958, hc23, hlam, hphi, p993_1, u3elo4]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [hlam, p993_0]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [h960, hlam, p993_0]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              rcases p993_3 (m.d 0 5) (by simp) with h1014 | h1014
                                              · linarith only [h1014, h884, hlam]
                                              · rcases p993_3 (m.d 1 5) (by simp) with h1016 | h1016
                                                · linarith only [h1016, h860, hlam, p993_1]
                                                · rcases p993_3 (m.d 2 5) (by simp) with h1018 | h1018
                                                  · linarith only [h1018, h958, hlam]
                                                  · rcases p993_3 (m.d 3 5) (by simp) with h1020 | h1020
                                                    · linarith only [h1020, h960, hlam]
                                                    · linarith only [h1020, h864, hlam]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              rcases p993_3 (m.d 0 5) (by simp) with h1023 | h1023
                                              · linarith only [h1023, h884, hlam]
                                              · linarith only [h1023, h860, hlam]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              rcases p993_3 (m.d 0 5) (by simp) with h1026 | h1026
                                              · linarith only [h1026, h884, hlam]
                                              · linarith only [h1026, h863, hlam]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [h864, hc03, hc45, hlam, hphi, ht34, p993_1]
                                            · have p993_0 := h993c.1
                                              have p993_1 := h993c.2.1
                                              have p993_2 := h993c.2.2.1
                                              have p993_3 := h993c.2.2.2
                                              linarith only [hlam, p993_0]
                                    · linarith only [h951, h986, hlam]
                                  · linarith only [h985, hlam, p962_0]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  linarith only [hc02, hlam, hphi, p962_1, u2elo1]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  linarith only [hlam, p962_0]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  rcases p962_3 (m.d 0 2) (by simp) with h1035 | h1035
                                  · linarith only [h0, h1035, hlam]
                                  · linarith only [h1035, h861, hlam]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  rcases p962_3 (m.d 0 2) (by simp) with h1038 | h1038
                                  · linarith only [h0, h1038, hlam]
                                  · linarith only [h1038, h862, hlam]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  rcases p962_3 (m.d 0 2) (by simp) with h1041 | h1041
                                  · linarith only [h0, h1041, hlam]
                                  · linarith only [h1041, h863, hlam]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  linarith only [h861, hlam, p962_0]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  linarith only [h949, hlam, p962_0]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  linarith only [hlam, p962_0]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  linarith only [h954, hlam, p962_1]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  linarith only [h956, hlam, p962_1]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  linarith only [h862, hlam, p962_0]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  linarith only [h950, hlam, p962_0]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  linarith only [h0, h860, h951, h958, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p962_1, u2elo0]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  linarith only [hlam, p962_0]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  linarith only [h958, hlam, p962_0]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  linarith only [h863, hlam, p962_0]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  linarith only [h951, hlam, p962_0]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  linarith only [h0, h860, h951, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p962_1, u2elo1]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  linarith only [h0, h860, h951, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p962_1, u2elo1]
                                · have p962_0 := h962c.1
                                  have p962_1 := h962c.2.1
                                  have p962_2 := h962c.2.2.1
                                  have p962_3 := h962c.2.2.2
                                  linarith only [hlam, p962_0]
                    · linarith only [h0, h951, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h950, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h859, h949, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · linarith only [h0, h860, h863, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1063 | h1063
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1064 | h1064
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1065 | h1065
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1066 | h1066
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1067 | h1067
                  · linarith only [h1063, h1067, h862, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · linarith only [h0, h1066, h1067, h859, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h1066, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h0, h1064, h1065, h859, h862, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1072 | h1072
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1073 | h1073
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1074 | h1074
                  · linarith only [h0, h1073, h1074, h859, h862, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1073, h1074, h859, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h1073, h859, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · linarith only [h0, h1072, h860, h862, hlam]
          · linarith only [h0, h1063, h860, hlam]
      · linarith only [h0, h859, h861, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1081 | h1081
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1082 | h1082
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1083 | h1083
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1084 | h1084
            · linarith only [h1084, h859, h860, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1086 | h1086
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1087 | h1087
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1088 | h1088
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1089 | h1089
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1090 | h1090
                      · linarith only [h1084, h1090, h859, h860, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h1087, h1090, h859, h860, hc23, hlam, hphi, u3elo4]
                    · linarith only [h0, h1083, h1089, hlam]
                  · linarith only [h0, h1082, h1088, hlam]
                · linarith only [h0, h1087, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1096 | h1096
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1097 | h1097
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1098 | h1098
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1099 | h1099
                      · linarith only [h1084, h1098, h1099, h859, h860, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                      · linarith only [h1096, h1099, h859, h860, hc23, hlam, hphi, u3elo4]
                    · linarith only [h0, h1096, h1098, h859, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · linarith only [h0, h1096, h1097, h859, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h1096, h859, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1105 | h1105
            · linarith only [h0, h1083, h1105, h859, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1107 | h1107
              · linarith only [h1082, h1083, h1107, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1109 | h1109
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1110 | h1110
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1111 | h1111
                    · linarith only [h0, h1083, h1109, h1111, h859, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1109, h1111, h859, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · linarith only [h0, h1082, h1109, h1110, h859, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h1109, h859, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1116 | h1116
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1117 | h1117
            · linarith only [h1117, h859, h860, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1119 | h1119
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1120 | h1120
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1121 | h1121
                  · linarith only [h1082, h1121, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1120, h1121, h859, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h1120, h859, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
              · linarith only [h1082, h1116, h1119, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1126 | h1126
            · linarith only [h0, h1116, h1126, h859, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1128 | h1128
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1129 | h1129
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1130 | h1130
                  · linarith only [h0, h1082, h1129, h1130, h859, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1129, h1130, h859, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h1129, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1134 | h1134
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1135 | h1135
                  · linarith only [h0, h1082, h1134, h1135, h859, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1134, h1135, h859, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                · linarith only [h0, h1134, h859, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
      · linarith only [h0, h1081, h859, hc13, hlam, hphi, u3elo2]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1140 | h1140
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1141 | h1141
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1142 | h1142
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1143 | h1143
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1144 | h1144
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1145 | h1145
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1146 | h1146
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1147 | h1147
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1148 | h1148
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1149 | h1149
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1150 | h1150
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1151 | h1151
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1152 | h1152
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1153 | h1153
                              · linarith only [h1141, h1150, h1153, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · linarith only [h0, h1141, h1150, h1152, h1153, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1156 | h1156
                              · linarith only [h1150, h1152, h1156, hlam]
                              · rcases h2bigk with h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c | h1158c
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [hlam, p1158_0]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [h0, hlam, p1158_0]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [h0, h1150, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1158_1, u2elo1]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  rcases p1158_3 (m.d 0 2) (by simp) with h1162 | h1162
                                  · rcases p1158_3 (m.d 1 2) (by simp) with h1163 | h1163
                                    · rcases p1158_3 (m.d 2 3) (by simp) with h1164 | h1164
                                      · linarith only [h1141, h1164, hlam]
                                      · linarith only [h1150, h1164, hlam]
                                    · linarith only [h1147, h1163, hlam]
                                  · linarith only [h1162, hlam, p1158_0]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  rcases p1158_3 (m.d 0 2) (by simp) with h1169 | h1169
                                  · rcases p1158_3 (m.d 1 2) (by simp) with h1170 | h1170
                                    · rcases p1158_3 (m.d 2 3) (by simp) with h1171 | h1171
                                      · linarith only [h1141, h1171, hlam]
                                      · linarith only [h1151, h1171, hlam]
                                    · linarith only [h1148, h1170, hlam]
                                  · linarith only [h1169, hlam, p1158_0]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [hc02, hlam, hphi, p1158_1, u2elo1]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [hlam, p1158_0]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [h1151, h1156, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1158_1, u2elo1]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  rcases p1158_3 (m.d 0 2) (by simp) with h1179 | h1179
                                  · linarith only [h0, h1179, hlam]
                                  · linarith only [h1142, h1179, hlam]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  rcases p1158_3 (m.d 0 2) (by simp) with h1182 | h1182
                                  · linarith only [h0, h1182, hlam]
                                  · linarith only [h1143, h1182, hlam]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [h1141, hlam, p1158_0]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [h1146, hlam, p1158_0]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [hlam, p1158_0]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [h1141, h1150, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1158_1, u2elo0]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [h0, h1141, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1158_1, u2elo1]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [h1142, hlam, p1158_0]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [h1147, hlam, p1158_0]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [h1150, hlam, p1158_0]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [hlam, p1158_0]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [h1152, hlam, p1158_0]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [h1143, hlam, p1158_0]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [h1148, hlam, p1158_0]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [h1151, hlam, p1158_0]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [h0, h1143, h1150, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1158_1, u2elo1]
                                · have p1158_0 := h1158c.1
                                  have p1158_1 := h1158c.2.1
                                  have p1158_2 := h1158c.2.2.1
                                  have p1158_3 := h1158c.2.2.2
                                  linarith only [hlam, p1158_0]
                          · linarith only [h1144, h1151, hc23, hlam, hphi, u3elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1201 | h1201
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1202 | h1202
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1203 | h1203
                              · rcases h2bigk with h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c | h1204c
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [hlam, p1204_0]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [h0, hlam, p1204_0]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [h0, h1201, h1203, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1204_1, u2elo1]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [h0, h1150, h1201, h1203, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1204_1, u2elo1]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  rcases p1204_3 (m.d 0 2) (by simp) with h1209 | h1209
                                  · rcases p1204_3 (m.d 1 2) (by simp) with h1210 | h1210
                                    · rcases p1204_3 (m.d 2 3) (by simp) with h1211 | h1211
                                      · linarith only [h1141, h1211, hlam]
                                      · linarith only [h1201, h1211, hlam]
                                    · linarith only [h1148, h1210, hlam]
                                  · linarith only [h1209, hlam, p1204_0]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [hc02, hlam, hphi, p1204_1, u2elo1]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [hlam, p1204_0]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [h1201, h1203, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1204_1, u2elo1]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [h1150, h1201, h1203, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1204_1, u2elo1]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  rcases p1204_3 (m.d 0 2) (by simp) with h1220 | h1220
                                  · linarith only [h0, h1220, hlam]
                                  · linarith only [h1143, h1220, hlam]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [h1141, hlam, p1204_0]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [h1146, hlam, p1204_0]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [hlam, p1204_0]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [h1150, hlam, p1204_1]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [h1150, h1201, h1203, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1204_1, u3elo3]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [h1142, hlam, p1204_0]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [h1147, hlam, p1204_0]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [h0, h1142, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1204_1, u2elo1]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [hlam, p1204_0]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [h0, h1142, h1201, h1203, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1204_1, u2elo1]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [h1143, hlam, p1204_0]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [h1148, hlam, p1204_0]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [h1201, hlam, p1204_0]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [h1202, hlam, p1204_1]
                                · have p1204_0 := h1204c.1
                                  have p1204_1 := h1204c.2.1
                                  have p1204_2 := h1204c.2.2.1
                                  have p1204_3 := h1204c.2.2.2
                                  linarith only [hlam, p1204_0]
                              · linarith only [h1145, h1150, h1201, h1203, hc04, hc35, hlam, hphi, ht0b, ht5b]
                            · linarith only [h1140, h1145, h1150, h1201, h1202, h859, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h1144, h1201, h859, hc23, hlam, hphi, u3elo1]
                      · linarith only [h1140, h1144, h1149, h859, hlam]
                    · linarith only [h0, h1148, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h1140, h1146, h1147, h859, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                · linarith only [h0, h1140, h1146, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1245 | h1245
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1246 | h1246
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1247 | h1247
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1248 | h1248
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1249 | h1249
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1250 | h1250
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1251 | h1251
                            · linarith only [h1142, h1145, h1251, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1253 | h1253
                              · linarith only [h1142, h1145, h1249, h1253, hlam]
                              · rcases h2bigk with h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c | h1255c
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [hlam, p1255_0]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [h0, hlam, p1255_0]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [h1250, h1253, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1255_1, u2elo0]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  rcases p1255_3 (m.d 0 2) (by simp) with h1259 | h1259
                                  · rcases p1255_3 (m.d 1 2) (by simp) with h1260 | h1260
                                    · rcases p1255_3 (m.d 2 3) (by simp) with h1261 | h1261
                                      · linarith only [h1141, h1261, hlam]
                                      · linarith only [h1249, h1261, hlam]
                                    · linarith only [h1246, h1260, hlam]
                                  · linarith only [h1259, hlam, p1255_0]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  rcases p1255_3 (m.d 0 2) (by simp) with h1266 | h1266
                                  · rcases p1255_3 (m.d 1 2) (by simp) with h1267 | h1267
                                    · rcases p1255_3 (m.d 2 3) (by simp) with h1268 | h1268
                                      · linarith only [h1141, h1268, hlam]
                                      · linarith only [h1250, h1268, hlam]
                                    · linarith only [h1247, h1267, hlam]
                                  · linarith only [h1266, hlam, p1255_0]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [hc02, hlam, hphi, p1255_1, u2elo1]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [hlam, p1255_0]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [h1250, h1253, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1255_1, u2elo1]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  rcases p1255_3 (m.d 0 2) (by simp) with h1276 | h1276
                                  · linarith only [h0, h1276, hlam]
                                  · linarith only [h1142, h1276, hlam]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  rcases p1255_3 (m.d 0 2) (by simp) with h1279 | h1279
                                  · linarith only [h0, h1279, hlam]
                                  · linarith only [h1143, h1279, hlam]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [h1141, hlam, p1255_0]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [h1245, hlam, p1255_0]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [hlam, p1255_0]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [h1141, h1249, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1255_1, u2elo0]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [h0, h1141, h1249, h1251, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1255_1, u2elo1]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [h1142, hlam, p1255_0]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [h1246, hlam, p1255_0]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [h1249, hlam, p1255_0]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [hlam, p1255_0]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [h1251, hlam, p1255_0]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [h1143, hlam, p1255_0]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [h1247, hlam, p1255_0]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [h1250, hlam, p1255_0]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [h1140, h1247, h1249, h859, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1255_1]
                                · have p1255_0 := h1255c.1
                                  have p1255_1 := h1255c.2.1
                                  have p1255_2 := h1255c.2.2.1
                                  have p1255_3 := h1255c.2.2.2
                                  linarith only [hlam, p1255_0]
                          · linarith only [h1144, h1250, h859, hc23, hlam, hphi, u3elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1298 | h1298
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1299 | h1299
                            · linarith only [h1142, h1145, h1299, hlam]
                            · linarith only [h1140, h1247, h1249, h1298, h1299, h859, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                          · linarith only [h1144, h1298, h859, hc23, hlam, hphi, u3elo1]
                      · linarith only [h1248, h859, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h0, h1247, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h1140, h1245, h1246, h859, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                · linarith only [h0, h1140, h1245, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · linarith only [h1140, h1144, h859, hlam]
          · linarith only [h1140, h1141, h1143, h859, hc23, hlam, hphi, u3elo1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1309 | h1309
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1310 | h1310
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1311 | h1311
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1312 | h1312
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1313 | h1313
                  · linarith only [h1141, h1142, h1313, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1313, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h1140, h1141, h1312, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h1140, h1142, h1311, hlam]
            · linarith only [h1140, h1310, h859, hlam]
          · linarith only [h1140, h1141, h1309, h859, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1320 | h1320
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1321 | h1321
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1322 | h1322
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1323 | h1323
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1324 | h1324
                · linarith only [h1141, h1324, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h1324, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1327 | h1327
                · linarith only [h1141, h1320, h1327, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h1140, h1327, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
            · linarith only [h1140, h1322, h859, hlam]
          · linarith only [h0, h1140, h1321, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1332 | h1332
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1333 | h1333
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1334 | h1334
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1335 | h1335
                · linarith only [h0, h1141, h1335, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h1140, h1335, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · linarith only [h0, h1140, h1320, h1334, hlam]
            · linarith only [h0, h1140, h1141, h1333, hlam]
          · linarith only [h0, h1140, h1332, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1341 | h1341
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1342 | h1342
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1343 | h1343
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1344 | h1344
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1345 | h1345
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1346 | h1346
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1347 | h1347
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1348 | h1348
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1349 | h1349
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1350 | h1350
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1351 | h1351
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1352 | h1352
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1353 | h1353
                              · linarith only [h1341, h1350, h1353, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                              · linarith only [h0, h1341, h1350, h1352, h1353, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1356 | h1356
                              · linarith only [h1350, h1352, h1356, hlam]
                              · rcases h2bigk with h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c | h1358c
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [hlam, p1358_0]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [h0, hlam, p1358_0]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [h0, h1351, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1358_1, u2elo1]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  rcases p1358_3 (m.d 0 2) (by simp) with h1362 | h1362
                                  · rcases p1358_3 (m.d 1 2) (by simp) with h1363 | h1363
                                    · rcases p1358_3 (m.d 2 3) (by simp) with h1364 | h1364
                                      · linarith only [h1341, h1364, hlam]
                                      · linarith only [h1350, h1364, hlam]
                                    · linarith only [h1347, h1363, hlam]
                                  · linarith only [h1362, hlam, p1358_0]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  rcases p1358_3 (m.d 0 2) (by simp) with h1369 | h1369
                                  · rcases p1358_3 (m.d 1 2) (by simp) with h1370 | h1370
                                    · rcases p1358_3 (m.d 2 3) (by simp) with h1371 | h1371
                                      · linarith only [h1341, h1371, hlam]
                                      · linarith only [h1351, h1371, hlam]
                                    · linarith only [h1348, h1370, hlam]
                                  · linarith only [h1369, hlam, p1358_0]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [hc02, hlam, hphi, p1358_1, u2elo1]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [hlam, p1358_0]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [h1351, h1356, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1358_1, u2elo1]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  rcases p1358_3 (m.d 0 2) (by simp) with h1379 | h1379
                                  · linarith only [h0, h1379, hlam]
                                  · linarith only [h1342, h1379, hlam]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  rcases p1358_3 (m.d 0 2) (by simp) with h1382 | h1382
                                  · linarith only [h0, h1382, hlam]
                                  · linarith only [h1343, h1382, hlam]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [h1341, hlam, p1358_0]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [h1346, hlam, p1358_0]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [hlam, p1358_0]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [h1341, h1350, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1358_1, u2elo0]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [h0, h1341, h1351, h1356, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1358_1, u2elo1]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [h1342, hlam, p1358_0]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [h1347, hlam, p1358_0]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [h1350, hlam, p1358_0]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [hlam, p1358_0]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [h1352, hlam, p1358_0]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [h1343, hlam, p1358_0]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [h1348, hlam, p1358_0]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [h1351, hlam, p1358_0]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [h0, h1343, h1350, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1358_1, u2elo1]
                                · have p1358_0 := h1358c.1
                                  have p1358_1 := h1358c.2.1
                                  have p1358_2 := h1358c.2.2.1
                                  have p1358_3 := h1358c.2.2.2
                                  linarith only [hlam, p1358_0]
                          · linarith only [h1344, h1351, hc23, hlam, hphi, u3elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1401 | h1401
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1402 | h1402
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1403 | h1403
                              · rcases h2bigk with h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c | h1404c
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [hlam, p1404_0]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [h0, hlam, p1404_0]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [h0, h1401, h1403, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1404_1, u2elo1]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [h0, h1350, h1401, h1403, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1404_1, u2elo1]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  rcases p1404_3 (m.d 0 2) (by simp) with h1409 | h1409
                                  · rcases p1404_3 (m.d 1 2) (by simp) with h1410 | h1410
                                    · rcases p1404_3 (m.d 2 3) (by simp) with h1411 | h1411
                                      · linarith only [h1341, h1411, hlam]
                                      · linarith only [h1401, h1411, hlam]
                                    · linarith only [h1348, h1410, hlam]
                                  · linarith only [h1409, hlam, p1404_0]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [hc02, hlam, hphi, p1404_1, u2elo1]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [hlam, p1404_0]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [h1401, h1403, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1404_1, u2elo1]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [h1350, h1401, h1403, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1404_1, u2elo1]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  rcases p1404_3 (m.d 0 2) (by simp) with h1420 | h1420
                                  · linarith only [h0, h1420, hlam]
                                  · linarith only [h1343, h1420, hlam]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [h1341, hlam, p1404_0]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [h1346, hlam, p1404_0]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [hlam, p1404_0]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [h1350, hlam, p1404_1]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [h1350, h1401, h1403, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1404_1, u3elo3]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [h1342, hlam, p1404_0]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [h1347, hlam, p1404_0]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [h0, h1342, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1404_1, u2elo1]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [hlam, p1404_0]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [h0, h1342, h1401, h1403, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1404_1, u2elo1]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [h1343, hlam, p1404_0]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [h1348, hlam, p1404_0]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [h1401, hlam, p1404_0]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [h1402, hlam, p1404_1]
                                · have p1404_0 := h1404c.1
                                  have p1404_1 := h1404c.2.1
                                  have p1404_2 := h1404c.2.2.1
                                  have p1404_3 := h1404c.2.2.2
                                  linarith only [hlam, p1404_0]
                              · linarith only [h1345, h1350, h1401, h1403, hc04, hc35, hlam, hphi, ht0b, ht5b]
                            · linarith only [h0, h1342, h1345, h1350, h1401, h1402, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h1344, h1401, hc23, hlam, hphi, u3elo0]
                      · linarith only [h1344, h1349, h859, hlam]
                    · linarith only [h0, h1348, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h1346, h1347, h859, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h1346, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1445 | h1445
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1446 | h1446
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1447 | h1447
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1448 | h1448
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1449 | h1449
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1450 | h1450
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1451 | h1451
                            · linarith only [h1341, h1345, h1449, h1451, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1453 | h1453
                              · linarith only [h0, h1140, h1342, h1345, h1449, h1453, hc01, hlam, hphi, ht12, u2elo1]
                              · rcases h2bigk with h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c | h1455c
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [hlam, p1455_0]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [h0, hlam, p1455_0]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [h0, h1450, h1453, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1455_1, u2elo1]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  rcases p1455_3 (m.d 0 2) (by simp) with h1459 | h1459
                                  · rcases p1455_3 (m.d 1 2) (by simp) with h1460 | h1460
                                    · rcases p1455_3 (m.d 2 3) (by simp) with h1461 | h1461
                                      · linarith only [h1341, h1461, hlam]
                                      · linarith only [h1449, h1461, hlam]
                                    · linarith only [h1446, h1460, hlam]
                                  · linarith only [h1459, hlam, p1455_0]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  rcases p1455_3 (m.d 0 2) (by simp) with h1466 | h1466
                                  · rcases p1455_3 (m.d 1 2) (by simp) with h1467 | h1467
                                    · rcases p1455_3 (m.d 2 3) (by simp) with h1468 | h1468
                                      · linarith only [h1341, h1468, hlam]
                                      · linarith only [h1450, h1468, hlam]
                                    · linarith only [h1447, h1467, hlam]
                                  · linarith only [h1466, hlam, p1455_0]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [hc02, hlam, hphi, p1455_1, u2elo1]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [hlam, p1455_0]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [h1450, h1453, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1455_1, u2elo1]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  rcases p1455_3 (m.d 0 2) (by simp) with h1476 | h1476
                                  · linarith only [h0, h1476, hlam]
                                  · linarith only [h1342, h1476, hlam]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  rcases p1455_3 (m.d 0 2) (by simp) with h1479 | h1479
                                  · linarith only [h0, h1479, hlam]
                                  · linarith only [h1343, h1479, hlam]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [h1341, hlam, p1455_0]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [h1445, hlam, p1455_0]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [hlam, p1455_0]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [h1341, h1449, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1455_1, u2elo0]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [h0, h1341, h1449, h1451, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1455_1, u2elo1]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [h1342, hlam, p1455_0]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [h1446, hlam, p1455_0]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [h1449, hlam, p1455_0]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [hlam, p1455_0]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [h1451, hlam, p1455_0]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [h1343, hlam, p1455_0]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [h1447, hlam, p1455_0]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [h1450, hlam, p1455_0]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [h0, h1343, h1449, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1455_1, u2elo1]
                                · have p1455_0 := h1455c.1
                                  have p1455_1 := h1455c.2.1
                                  have p1455_2 := h1455c.2.2.1
                                  have p1455_3 := h1455c.2.2.2
                                  linarith only [hlam, p1455_0]
                          · linarith only [h1344, h1450, hc23, hlam, hphi, u3elo0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1498 | h1498
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1499 | h1499
                            · linarith only [h1342, h1345, h1499, hlam]
                            · linarith only [h1449, h1498, h1499, hlam]
                          · linarith only [h1344, h1498, h859, hc23, hlam, hphi, u3elo1]
                      · linarith only [h1344, h1448, h859, hlam]
                    · linarith only [h0, h1447, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h1446, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h1445, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1507 | h1507
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1508 | h1508
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1509 | h1509
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1510 | h1510
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1511 | h1511
                      · linarith only [h1344, h1511, hc03, hlam, hphi, u3elo1]
                      · linarith only [h1511, h859, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h0, h1510, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h0, h1342, h1509, hlam]
                · linarith only [h0, h1508, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1517 | h1517
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1518 | h1518
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1519 | h1519
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h1520 | h1520
                      · linarith only [h1344, h1517, h1520, h859, hc01, hlam, hphi, ht12, u2elo1]
                      · linarith only [h1520, h859, hc01, hlam, hphi, ht12, ht23, u3elo4]
                    · linarith only [h1343, h1519, hc12, hlam, hphi, u2elo0]
                  · linarith only [h0, h1518, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h1517, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1526 | h1526
            · linarith only [h1341, h1343, h1526, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1528 | h1528
              · linarith only [h1342, h1343, h1528, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1530 | h1530
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1531 | h1531
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h1532 | h1532
                    · linarith only [h1343, h1532, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1532, hc01, hlam, hphi, ht12, u2elo4]
                  · linarith only [h1530, h1531, h859, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h1341, h1343, h1530, hc01, hlam, hphi, ht12, u2elo4]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1537 | h1537
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1538 | h1538
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1539 | h1539
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1540 | h1540
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1541 | h1541
                  · linarith only [h1342, h1541, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1541, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h1540, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h1341, h1342, h1538, h1539, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1546 | h1546
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1547 | h1547
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1548 | h1548
                  · linarith only [h1342, h1548, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1548, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h1547, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h1342, h1537, h1546, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1553 | h1553
            · linarith only [h1341, h1537, h1553, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1555 | h1555
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1556 | h1556
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1557 | h1557
                  · linarith only [h1341, h1342, h1557, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1557, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h1556, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1561 | h1561
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1562 | h1562
                  · linarith only [h1342, h1562, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1562, hc01, hlam, hphi, ht12, u2elo3]
                · linarith only [h0, h1561, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1566 | h1566
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1567 | h1567
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1568 | h1568
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1569 | h1569
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1570 | h1570
                · linarith only [h1341, h1570, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h1570, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1573 | h1573
                · linarith only [h1341, h1566, h1573, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h1573, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h1341, h1567, h1568, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1577 | h1577
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1578 | h1578
              · linarith only [h1566, h1567, h1578, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1580 | h1580
                · linarith only [h1341, h1566, h1580, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h1580, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1583 | h1583
              · linarith only [h1341, h1566, h1577, h1583, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1585 | h1585
                · linarith only [h1341, h1566, h1585, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                · linarith only [h0, h1585, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1588 | h1588
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1589 | h1589
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1590 | h1590
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1591 | h1591
                · linarith only [h1341, h1588, h1591, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                · linarith only [h0, h1591, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · linarith only [h1566, h1588, h1590, hlam]
            · linarith only [h1341, h1588, h1589, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h1596 | h1596
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1597 | h1597
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1598 | h1598
                · linarith only [h1341, h1598, hc02, hlam, hphi, u2elo1]
                · linarith only [h0, h1598, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1601 | h1601
                · linarith only [h0, h1341, h1601, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h1601, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h1604 | h1604
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1605 | h1605
                · linarith only [h0, h1341, h1605, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h1605, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h1608 | h1608
                · linarith only [h0, h1341, h1608, hc01, hlam, hphi, ht12, u2elo1]
                · linarith only [h0, h1608, hc01, hlam, hphi, ht12, u2elo2]

set_option maxHeartbeats 3222000 in
set_option maxHeartbeats 3222000 in
theorem r1l7_22_13_15_M_LI_L_0_L_I (m : N7Model)
    (hb2 : CMSig2_7_M_LI m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h2elo := hb2.1
  have h2bigk := hb2.2.2.2
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_22_13_15_M_LI_L_0_L_I_x0 m hb2 hb3 hb5 h0
  · exact r1l7_22_13_15_M_LI_L_0_L_I_x1 m hb2 hb3 hb5 h0

end R2N4
