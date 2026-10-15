import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_58S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3642000 in
set_option maxHeartbeats 3642000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_0_L_0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h3elo := hb3.1
  have h4elo := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h897 | h897
  · rcases m.htr 0 1 4 (by decide) (by decide) with h898 | h898
    · rcases m.htr 0 1 5 (by decide) (by decide) with h899 | h899
      · rcases m.htr 0 2 3 (by decide) (by decide) with h900 | h900
        · rcases m.htr 0 2 4 (by decide) (by decide) with h901 | h901
          · rcases m.htr 0 3 4 (by decide) (by decide) with h902 | h902
            · rcases m.htr 0 3 5 (by decide) (by decide) with h903 | h903
              · rcases m.htr 0 4 5 (by decide) (by decide) with h904 | h904
                · rcases m.htr 1 2 3 (by decide) (by decide) with h905 | h905
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h906 | h906
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h907 | h907
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h908 | h908
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h909 | h909
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h910 | h910
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h911 | h911
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h912 | h912
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h913 | h913
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h914 | h914
                                    · linarith only [h0, h897, h905, h911, h914, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                    · linarith only [h898, h906, h913, h914, hc34, hlam, hphi, u4elo0]
                                  · linarith only [h904, h913, hc24, hlam, hphi, u4elo0]
                                · linarith only [h903, h912, hc23, hlam, hphi, u3elo0]
                              · linarith only [h902, h911, hc23, hlam, hphi, u3elo0]
                            · linarith only [h904, h910, hc14, hlam, hphi, u4elo0]
                          · linarith only [h903, h909, hc13, hlam, hphi, u3elo0]
                        · linarith only [h902, h905, h908, hc23, hlam, hphi, u3elo0]
                      · linarith only [h0, h899, h907, hlam]
                    · linarith only [h0, h897, h905, h906, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h905, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h926 | h926
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h927 | h927
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h928 | h928
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h929 | h929
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h930 | h930
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h931 | h931
                            · linarith only [h904, h931, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h933 | h933
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h934 | h934
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h935 | h935
                                  · linarith only [h898, h904, h927, h935, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h937 | h937
                                    · linarith only [h897, h904, h926, h933, h937, hc01, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                    · rcases h0bigk with h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c | h939c
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [hlam, p939_0]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [h0, hlam, p939_1]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [h0, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p939_1]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [h0, h898, h927, h933, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p939_1]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p939_1]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p939_1]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [hlam, p939_0]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [h0, h897, h926, h934, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p939_1]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        rcases p939_3 (m.d 0 1) (by simp) with h948 | h948
                                        · linarith only [h0, h948, hlam]
                                        · linarith only [h898, h948, hlam]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        rcases p939_3 (m.d 0 1) (by simp) with h951 | h951
                                        · linarith only [h0, h951, hlam]
                                        · linarith only [h899, h951, hlam]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [h897, hlam, p939_1]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [h900, hlam, p939_1]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [hlam, p939_0]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [h898, h927, h933, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p939_1, u3elo0]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [h898, h904, h927, h933, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p939_1, u3elo0]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [h898, hlam, p939_0]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [h901, hlam, p939_0]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [h902, hlam, p939_0]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [hlam, p939_0]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [h904, hlam, p939_0]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [h899, hlam, p939_0]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [h0, h897, h926, h934, h937, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p939_1]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [h903, hlam, p939_0]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [h898, h904, h927, h933, hc34, hlam, hphi, p939_1, u4elo4]
                                      · have p939_0 := h939c.1
                                        have p939_1 := h939c.2.1
                                        have p939_2 := h939c.2.2.1
                                        have p939_3 := h939c.2.2.2
                                        linarith only [hlam, p939_0]
                                · linarith only [h903, h934, hc23, hlam, hphi, u3elo0]
                              · linarith only [h902, h933, hc23, hlam, hphi, u3elo0]
                          · linarith only [h903, h930, hc13, hlam, hphi, u3elo0]
                        · linarith only [h902, h926, h929, hc23, hlam, hphi, u3elo0]
                      · linarith only [h0, h899, h928, hlam]
                    · linarith only [h0, h897, h926, h927, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h926, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h976 | h976
                · linarith only [h902, h903, h976, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h978 | h978
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h979 | h979
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h980 | h980
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h981 | h981
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h982 | h982
                          · linarith only [h897, h903, h982, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h984 | h984
                            · linarith only [h976, h984, hc04, hlam, hphi, u4elo1]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h986 | h986
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h987 | h987
                                · linarith only [h897, h903, h978, h987, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h989 | h989
                                  · linarith only [h897, h898, h903, h976, h978, h979, h986, h989, hc34, hlam, hphi, u4elo0]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h991 | h991
                                    · linarith only [h897, h903, h976, h978, h986, h991, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                    · linarith only [h902, h903, h991, hc34, hlam, hphi, u4elo4]
                              · linarith only [h897, h903, h981, h986, hc23, hlam, hphi, u3elo4]
                        · linarith only [h902, h903, h981, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h899, h980, hlam]
                    · linarith only [h0, h901, h902, h903, h979, hc01, hlam, hphi, ht12, ht23, u3elo4]
                  · linarith only [h0, h978, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h999 | h999
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1000 | h1000
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1001 | h1001
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1002 | h1002
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1003 | h1003
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1004 | h1004
                        · linarith only [h0, h1004, h897, h902, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1006 | h1006
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1007 | h1007
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1008 | h1008
                              · linarith only [h1006, h1008, h897, h902, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1010 | h1010
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1011 | h1011
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1012 | h1012
                                    · rcases h0bigk with h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c | h1013c
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [hlam, p1013_0]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [h0, hlam, p1013_1]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [h0, h1001, h1010, h1012, h897, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1013_1]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [h0, h1001, h1010, h1012, h897, h902, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1013_1]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1013_1]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1013_1]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [hlam, p1013_0]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [h0, h1001, h1010, h1012, h897, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1013_1]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [h0, h1001, h1010, h1012, h897, h902, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1013_1]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        rcases p1013_3 (m.d 0 1) (by simp) with h1023 | h1023
                                        · linarith only [h0, h1023, hlam]
                                        · linarith only [h1023, h899, hlam]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [h897, hlam, p1013_1]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [h900, hlam, p1013_1]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [hlam, p1013_0]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [h902, hlam, p1013_1]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [h1003, h1010, h1012, h899, h902, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1013_1, u4elo3]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [h898, hlam, p1013_0]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [h901, hlam, p1013_0]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [hc03, hlam, hphi, ht34, p1013_1, u4elo0]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [hlam, p1013_0]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [h1003, h1010, h1012, h899, h902, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1013_1, u4elo3]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [h899, hlam, p1013_0]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [h0, h1001, h1010, h1012, h897, hc05, hc45, hlam, hphi, ht0b, ht5b, p1013_1]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [h999, hlam, p1013_0]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [h1000, hlam, p1013_1]
                                      · have p1013_0 := h1013c.1
                                        have p1013_1 := h1013c.2.1
                                        have p1013_2 := h1013c.2.2.1
                                        have p1013_3 := h1013c.2.2.2
                                        linarith only [hlam, p1013_0]
                                    · linarith only [h1001, h1010, h1012, h897, h902, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                                  · linarith only [h1007, h1008, h1010, h1011, h898, hc01, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h1010, h999, hc23, hlam, hphi, u3elo0]
                            · linarith only [h1000, h1007, h902, hc14, hlam, hphi, u4elo3]
                          · linarith only [h1006, h902, h999, hc13, hlam, hphi, ht34, u4elo3]
                      · linarith only [h0, h1003, h899, hlam]
                    · linarith only [h0, h1001, h1002, h897, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1001, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1000, h902, h999, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1050 | h1050
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1051 | h1051
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1052 | h1052
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1053 | h1053
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1054 | h1054
                        · linarith only [h0, h1054, h897, h902, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1056 | h1056
                          · linarith only [h1056, h897, h999, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1058 | h1058
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1059 | h1059
                              · linarith only [h1051, h1059, h897, h902, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1061 | h1061
                                · linarith only [h1061, h999, hc03, hlam, hphi, u3elo2]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1063 | h1063
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1064 | h1064
                                    · rcases h0bigk with h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c | h1065c
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [hlam, p1065_0]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [h0, hlam, p1065_1]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [h0, h1051, h897, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1065_1]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [h0, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1065_1]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1065_1]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1065_1]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [hlam, p1065_0]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        rcases p1065_3 (m.d 0 1) (by simp) with h1073 | h1073
                                        · linarith only [h0, h1073, hlam]
                                        · linarith only [h1073, h897, hlam]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [h0, h1052, h1063, h898, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1065_1]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        rcases p1065_3 (m.d 0 1) (by simp) with h1077 | h1077
                                        · linarith only [h0, h1077, hlam]
                                        · linarith only [h1077, h899, hlam]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [h897, hlam, p1065_1]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [h900, hlam, p1065_1]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [hlam, p1065_0]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [h902, hlam, p1065_1]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [h999, hlam, p1065_1]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [h898, hlam, p1065_0]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [h901, hlam, p1065_0]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [h1051, h897, hc23, hlam, hphi, ht34, p1065_1, u4elo0]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [hlam, p1065_0]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [h1051, h1056, h899, h902, hc23, hlam, hphi, ht34, p1065_1, u4elo3]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [h899, hlam, p1065_0]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [h0, h1052, h1063, h898, hc05, hc45, hlam, hphi, ht0b, ht5b, p1065_1]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [h1051, h897, h999, hc23, hlam, hphi, p1065_1, u3elo4]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [h1050, hlam, p1065_1]
                                      · have p1065_0 := h1065c.1
                                        have p1065_1 := h1065c.2.1
                                        have p1065_2 := h1065c.2.2.1
                                        have p1065_3 := h1065c.2.2.2
                                        linarith only [hlam, p1065_0]
                                    · linarith only [h1052, h1063, h1064, h902, hc04, hlam, hphi, u4elo1]
                                  · linarith only [h1058, h1059, h1063, h898, hc23, hlam, hphi, ht34, u4elo0]
                            · linarith only [h1050, h1058, h902, hc14, hlam, hphi, u4elo3]
                      · linarith only [h0, h1053, h899, hlam]
                    · linarith only [h0, h1050, h1052, h898, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo2]
                  · linarith only [h0, h1051, h897, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1101 | h1101
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1102 | h1102
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1103 | h1103
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1104 | h1104
                        · linarith only [h1050, h1104, h897, h902, hc34, hlam, hphi, u4elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1106 | h1106
                          · linarith only [h1106, h897, h999, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1108 | h1108
                            · linarith only [h0, h1050, h1108, h898, h902, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1110 | h1110
                              · linarith only [h1101, h1110, h897, h902, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1112 | h1112
                                · linarith only [h1101, h1112, h897, h999, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1114 | h1114
                                  · linarith only [h1050, h1102, h1114, h898, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1116 | h1116
                                    · linarith only [h1050, h1101, h1116, h897, h902, hc23, hlam, hphi, u3elo3]
                                    · linarith only [h1101, h1116, h897, h902, hc23, hlam, hphi, ht34, u4elo4]
                      · linarith only [h0, h1103, h899, hlam]
                    · linarith only [h0, h1102, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1101, h897, hc13, hlam, hphi, u3elo2]
          · linarith only [h0, h897, h901, hc13, hlam, hphi, ht34, u4elo2]
        · linarith only [h0, h897, h900, hc13, hlam, hphi, u3elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1124 | h1124
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1125 | h1125
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1126 | h1126
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1127 | h1127
              · linarith only [h1127, h897, h899, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1129 | h1129
                · linarith only [h1126, h1129, h897, h899, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1131 | h1131
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1132 | h1132
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1133 | h1133
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1134 | h1134
                        · linarith only [h1129, h1134, h897, h899, hc34, hlam, hphi, u4elo4]
                        · linarith only [h1126, h1127, h1134, hc13, hlam, hphi, u3elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1137 | h1137
                        · linarith only [h1129, h1137, h897, h899, hc34, hlam, hphi, u4elo4]
                        · linarith only [h1126, h1127, h1137, hc13, hlam, hphi, u3elo4]
                    · linarith only [h0, h1131, h1132, h897, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1131, h897, hc13, hlam, hphi, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1142 | h1142
              · linarith only [h1126, h1142, h897, h899, hc13, hlam, hphi, ht34, u4elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1144 | h1144
                · linarith only [h1144, h898, h899, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1146 | h1146
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1147 | h1147
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1148 | h1148
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1149 | h1149
                        · linarith only [h1126, h1144, h1149, h897, hc34, hlam, hphi, u4elo4]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1151 | h1151
                          · linarith only [h1142, h1144, h1149, h1151, h898, h899, hc03, hlam, hphi, ht34, u4elo4]
                          · linarith only [h1146, h1151, h897, h899, hc23, hlam, hphi, u3elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1154 | h1154
                        · linarith only [h1126, h1154, h897, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1156 | h1156
                          · linarith only [h0, h1148, h1154, h1156, h898, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · linarith only [h0, h1146, h1148, h1154, h1156, h898, hc23, hlam, hphi, u3elo4]
                    · linarith only [h0, h1146, h1147, h897, hc23, hlam, hphi, ht34, u4elo2]
                  · linarith only [h0, h1146, h897, hc13, hlam, hphi, u3elo2]
          · linarith only [h0, h1125, h897, hc13, hlam, hphi, ht34, u4elo2]
        · linarith only [h0, h1124, h897, hc13, hlam, hphi, u3elo2]
    · linarith only [h897, h898, hc13, hlam, hphi, ht34, u4elo1]
  · rcases m.htr 0 1 4 (by decide) (by decide) with h1164 | h1164
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1165 | h1165
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1166 | h1166
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1167 | h1167
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1168 | h1168
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1169 | h1169
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1170 | h1170
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1171 | h1171
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1172 | h1172
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1173 | h1173
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1174 | h1174
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1175 | h1175
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1176 | h1176
                            · linarith only [h1164, h1176, h897, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h1170, h1172, h1176, hc24, hlam, hphi, u4elo0]
                          · linarith only [h1164, h1172, h1175, h897, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h1174, h897, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1165, h1173, h897, hc02, hlam, hphi, ht23, u3elo1]
                    · linarith only [h1164, h1167, h1171, h1172, h897, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h1164, h1171, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1184 | h1184
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1185 | h1185
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1186 | h1186
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1187 | h1187
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1188 | h1188
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1189 | h1189
                            · linarith only [h1164, h1170, h1184, h1189, h897, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1191 | h1191
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1192 | h1192
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1193 | h1193
                                  · linarith only [h1170, h1193, hc04, hlam, hphi, u4elo2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1195 | h1195
                                    · linarith only [h1170, h1191, h1195, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
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
                                        linarith only [h0, hlam, p1197_1]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [h897, hlam, p1197_0]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [h897, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1197_1, u3elo1]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [h897, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1197_1, u3elo1]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1197_1]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [hlam, p1197_0]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [h0, h1164, h1185, h1191, h897, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1197_1]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        rcases p1197_3 (m.d 0 1) (by simp) with h1206 | h1206
                                        · linarith only [h0, h1206, hlam]
                                        · linarith only [h1164, h1206, hlam]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        rcases p1197_3 (m.d 0 1) (by simp) with h1209 | h1209
                                        · linarith only [h0, h1209, hlam]
                                        · linarith only [h1165, h1209, hlam]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [h1165, h1185, h1189, h1191, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1197_1]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [h1166, hlam, p1197_1]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [hlam, p1197_0]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [h1164, h1185, h1191, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1197_1, u3elo0]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [h1164, h1170, h1185, h1191, h897, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1197_1, u3elo1]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [h1164, hlam, p1197_0]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [h1167, hlam, p1197_0]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [h1168, hlam, p1197_0]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [hlam, p1197_0]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [h1170, hlam, p1197_0]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [h1165, hlam, p1197_0]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [h0, h1165, h1185, h1189, h1191, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1197_1]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [h1169, hlam, p1197_0]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [h0, h1164, h1165, h1185, h1191, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1197_1]
                                      · have p1197_0 := h1197c.1
                                        have p1197_1 := h1197c.2.1
                                        have p1197_2 := h1197c.2.2.1
                                        have p1197_3 := h1197c.2.2.2
                                        linarith only [hlam, p1197_0]
                                · linarith only [h1169, h1192, h897, hc23, hlam, hphi, u3elo1]
                              · linarith only [h1168, h1191, h897, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1188, h897, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h1164, h1185, h1187, h897, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h1165, h1186, h897, hc12, hlam, hphi, ht23, u3elo1]
                    · linarith only [h0, h1185, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1164, h1184, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h1165, h1169, h897, hlam]
            · linarith only [h1164, h1168, h897, hc14, hlam, hphi, u4elo3]
          · linarith only [h1166, h1167, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1237 | h1237
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1238 | h1238
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1239 | h1239
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1240 | h1240
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1241 | h1241
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1242 | h1242
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1243 | h1243
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1244 | h1244
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1245 | h1245
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1246 | h1246
                            · linarith only [h0, h1164, h1166, h1241, h1246, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                            · linarith only [h1240, h1242, h1246, hc24, hlam, hphi, u4elo0]
                          · linarith only [h0, h1164, h1166, h1241, h1242, h1245, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h0, h1166, h1241, h1244, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1166, h1241, h1243, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h1164, h1166, h1241, h1242, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h1164, h1241, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1254 | h1254
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1255 | h1255
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1256 | h1256
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1257 | h1257
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1258 | h1258
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1259 | h1259
                            · linarith only [h0, h1164, h1166, h1240, h1259, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1261 | h1261
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1262 | h1262
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1263 | h1263
                                  · linarith only [h1240, h1263, hc04, hlam, hphi, u4elo2]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1265 | h1265
                                    · linarith only [h1164, h1240, h1255, h1261, h1265, hlam]
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
                                        linarith only [h0, hlam, p1267_1]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [h897, hlam, p1267_0]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [h0, h1164, h1166, h1254, h1255, h1261, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1267_1, u3elo1]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [h0, h1166, h1254, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1267_1, u3elo1]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [h1166, h1254, hc01, hlam, hphi, ht12, ht23, p1267_1, u3elo1]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [hlam, p1267_0]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [h1166, hlam, p1267_0]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [h1164, h1166, h1254, h1255, h1261, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1267_1, u3elo1]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [h1164, h1166, h1240, h1254, h1255, h1261, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1267_1, u3elo1]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [h1165, h1166, h1254, h1255, h1259, h1261, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1267_1, u3elo1]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [h1166, h1254, hc02, hlam, hphi, ht23, p1267_1, u3elo1]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [hlam, p1267_0]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [h1164, h1166, h1254, h1255, h1261, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1267_1, u3elo1]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [h1164, h1166, h1240, h1254, h1255, h1261, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1267_1, u3elo1]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [h1164, hlam, p1267_0]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [h1237, hlam, p1267_0]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [h1238, hlam, p1267_0]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [hlam, p1267_0]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [h1240, hlam, p1267_0]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [h1165, hlam, p1267_0]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [h0, h1165, h1255, h1259, h1261, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p1267_1]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [h1239, hlam, p1267_0]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [h0, h1164, h1165, h1255, h1261, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1267_1]
                                      · have p1267_0 := h1267c.1
                                        have p1267_1 := h1267c.2.1
                                        have p1267_2 := h1267c.2.2.1
                                        have p1267_3 := h1267c.2.2.2
                                        linarith only [hlam, p1267_0]
                                · linarith only [h0, h1166, h1262, hc01, hlam, hphi, ht12, ht23, u3elo4]
                              · linarith only [h0, h1165, h1166, h1257, h1259, h1261, hlam]
                          · linarith only [h1258, h897, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h0, h1164, h1166, h1254, h1255, h1257, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h0, h1164, h1166, h1254, h1255, h1256, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h1166, h1254, h1255, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h1164, h1254, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · linarith only [h1165, h1239, h897, hlam]
            · linarith only [h0, h1164, h1166, h1238, hc14, hlam, hphi, u4elo3]
          · linarith only [h0, h1164, h1237, hc14, hlam, hphi, u4elo2]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1303 | h1303
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1304 | h1304
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1305 | h1305
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1306 | h1306
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1307 | h1307
                · linarith only [h1164, h1165, h1307, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1309 | h1309
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1310 | h1310
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1311 | h1311
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1312 | h1312
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1313 | h1313
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1314 | h1314
                            · linarith only [h1164, h1165, h1307, h1314, hc04, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h1164, h1165, h1314, hc14, hlam, hphi, u4elo4]
                          · linarith only [h1306, h1313, h897, hlam]
                        · linarith only [h1164, h1312, h897, hc14, hlam, hphi, u4elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1319 | h1319
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1320 | h1320
                          · linarith only [h1309, h1311, h1320, hlam]
                          · linarith only [h1164, h1303, h1306, h1310, h1320, h897, hc02, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h1164, h1310, h1319, h897, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h0, h1164, h1304, h1310, h897, hc02, hlam, hphi, ht23, u3elo1]
                  · linarith only [h0, h1309, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1326 | h1326
                · linarith only [h1164, h1165, h1326, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1328 | h1328
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1329 | h1329
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1330 | h1330
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1331 | h1331
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1332 | h1332
                          · linarith only [h1306, h1332, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1164, h1329, h1332, h897, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h1164, h1329, h1331, h897, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1336 | h1336
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1337 | h1337
                          · linarith only [h1164, h1306, h1328, h1329, h1330, h1337, h897, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h1164, h1329, h1337, h897, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h1164, h1329, h1336, h897, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                    · linarith only [h0, h1329, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1303, h1328, hlam]
            · linarith only [h1164, h1305, h897, hc14, hlam, hphi, u4elo3]
          · linarith only [h1303, h1304, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1345 | h1345
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1346 | h1346
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1347 | h1347
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1348 | h1348
                · linarith only [h1164, h1165, h1348, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1350 | h1350
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1351 | h1351
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1352 | h1352
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1353 | h1353
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1354 | h1354
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1355 | h1355
                            · linarith only [h0, h1164, h1303, h1348, h1350, h1355, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                            · linarith only [h1164, h1165, h1351, h1355, hc24, hlam, hphi, u4elo4]
                          · linarith only [h0, h1164, h1303, h1347, h1350, h1351, h1354, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                        · linarith only [h0, h1164, h1303, h1350, h1351, h1353, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h0, h1164, h1303, h1350, h1351, h1352, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h1164, h1303, h1350, h1351, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · linarith only [h0, h1164, h1350, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1363 | h1363
                · linarith only [h1164, h1347, h1363, h897, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1365 | h1365
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1366 | h1366
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1367 | h1367
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1368 | h1368
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1369 | h1369
                          · linarith only [h0, h1303, h1347, h1369, hc01, hlam, hphi, ht12, ht23, u3elo1]
                          · linarith only [h1164, h1366, h1369, h897, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h0, h1164, h1303, h1365, h1366, h1368, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h0, h1164, h1303, h1365, h1366, h1367, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h0, h1303, h1365, h1366, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h1164, h1365, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
            · linarith only [h0, h1164, h1303, h1346, hc14, hlam, hphi, u4elo3]
          · linarith only [h0, h1164, h1345, hc14, hlam, hphi, u4elo2]
    · rcases m.htr 0 1 5 (by decide) (by decide) with h1378 | h1378
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1379 | h1379
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1380 | h1380
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1381 | h1381
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1382 | h1382
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1383 | h1383
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1384 | h1384
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1385 | h1385
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1386 | h1386
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1387 | h1387
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1388 | h1388
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1389 | h1389
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1390 | h1390
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1391 | h1391
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1392 | h1392
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1393 | h1393
                                    · rcases h0bigk with h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c | h1394c
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [hlam, p1394_0]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h0, hlam, p1394_1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h897, hlam, p1394_0]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1164, hlam, p1394_1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h0, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p1394_1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1394_1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [hlam, p1394_0]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h0, h1378, h1386, h1391, h1393, h897, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1394_1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h0, h1164, h1378, h1386, h1391, h1393, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1394_1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        rcases p1394_3 (m.d 0 1) (by simp) with h1404 | h1404
                                        · linarith only [h0, h1404, hlam]
                                        · linarith only [h1378, h1404, hlam]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1378, h1386, h1391, h1393, hc03, hc45, hlam, hphi, ht0b, ht5b, p1394_1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1379, hlam, p1394_1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [hlam, p1394_0]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1164, h1378, h1386, h1391, h1393, h897, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1394_1, u3elo1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1378, h1386, h1391, h1393, h897, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1394_1, u3elo1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1378, h1386, h1391, h1393, hc04, hc45, hlam, hphi, ht0b, ht5b, p1394_1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1380, hlam, p1394_0]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1381, hlam, p1394_0]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [hlam, p1394_0]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1164, h1378, h1386, h1391, h1393, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1394_1, u4elo1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1378, hlam, p1394_0]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h0, h1378, h1386, h1391, h1393, hc05, hc45, hlam, hphi, ht0b, ht5b, p1394_1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1382, hlam, p1394_0]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [h1383, hlam, p1394_1]
                                      · have p1394_0 := h1394c.1
                                        have p1394_1 := h1394c.2.1
                                        have p1394_2 := h1394c.2.2.1
                                        have p1394_3 := h1394c.2.2.2
                                        linarith only [hlam, p1394_0]
                                    · linarith only [h1164, h1383, h1393, hc34, hlam, hphi, u4elo1]
                                  · linarith only [h1378, h1389, h1392, h897, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · linarith only [h1382, h1390, h1391, h897, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                              · linarith only [h1381, h1390, h897, hc23, hlam, hphi, u3elo1]
                            · linarith only [h1164, h1378, h1386, h1389, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                          · linarith only [h1378, h1386, h1388, h897, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                        · linarith only [h1378, h1386, h1387, h897, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                      · linarith only [h1378, h1386, h897, hc12, hlam, hphi, ht23, u3elo1]
                    · linarith only [h1378, h1380, h1384, h1385, h897, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · linarith only [h0, h1378, h1384, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h1164, h1378, h1383, hlam]
              · linarith only [h1164, h1378, h1381, h1382, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1434 | h1434
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1435 | h1435
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1436 | h1436
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1437 | h1437
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1438 | h1438
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1439 | h1439
                        · linarith only [h1381, h1439, hc03, hlam, hphi, u3elo1]
                        · linarith only [h1378, h1438, h1439, h897, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                      · linarith only [h1378, h1436, h1438, h897, hlam]
                    · linarith only [h0, h1380, h1437, hlam]
                  · linarith only [h0, h1379, h1436, hlam]
                · linarith only [h1378, h1381, h1435, h897, hlam]
              · linarith only [h1378, h1434, h897, hlam]
          · linarith only [h1379, h1380, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1448 | h1448
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1449 | h1449
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1450 | h1450
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1451 | h1451
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1452 | h1452
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1453 | h1453
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1454 | h1454
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1455 | h1455
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1456 | h1456
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1457 | h1457
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1458 | h1458
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1459 | h1459
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1460 | h1460
                                  · linarith only [h1379, h1448, h1452, h1460, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h1379, h1448, h1451, h1452, h1458, h1460, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · linarith only [h1164, h1379, h1448, h1459, hc01, hlam, hphi, ht12, ht23, u3elo4]
                              · linarith only [h1164, h1379, h1448, h1458, hc01, hlam, hphi, ht12, ht23, u3elo3]
                            · linarith only [h1164, h1378, h1454, h1457, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                          · linarith only [h1379, h1448, h1452, h1456, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h1379, h1448, h1449, h1452, h1455, hlam]
                      · linarith only [h1379, h1452, h1454, hc02, hc25, hlam, hphi]
                    · linarith only [h1164, h1378, h1379, h1448, h1452, h1453, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h1378, h1452, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h1164, h1378, h1451, hlam]
              · linarith only [h1164, h1378, h1449, h1450, hc34, hlam, hphi, u4elo1]
            · linarith only [h1379, h1448, h1449, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1474 | h1474
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1475 | h1475
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1476 | h1476
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1477 | h1477
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1478 | h1478
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1479 | h1479
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1480 | h1480
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1481 | h1481
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1482 | h1482
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1483 | h1483
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1484 | h1484
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1485 | h1485
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1486 | h1486
                                    · rcases h0bigk with h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c | h1487c
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [hlam, p1487_0]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h0, hlam, p1487_1]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h897, hlam, p1487_0]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h1164, hlam, p1487_1]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h0, h1448, h1478, h1480, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1487_1, u3elo1]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h1448, h1478, h1480, hc01, hlam, hphi, ht12, ht23, p1487_1, u3elo1]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [hlam, p1487_0]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h1379, hlam, p1487_0]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h1448, hlam, p1487_1]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h1378, h1448, h1478, h1479, h1480, h1484, h1486, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1487_1, u3elo1]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h1378, h1479, h1484, h1486, hc03, hc45, hlam, hphi, ht0b, ht5b, p1487_1]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h897, hc02, hlam, hphi, ht23, p1487_1, u3elo1]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [hlam, p1487_0]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h897, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1487_1, u3elo1]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h1378, h1479, h1484, h1486, h897, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1487_1, u3elo1]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h1378, h1479, h1484, h1486, hc04, hc45, hlam, hphi, ht0b, ht5b, p1487_1]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h0, h1378, h1448, h1478, h1479, h1480, h1484, h1486, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1487_1, u3elo1]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h1474, hlam, p1487_0]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [hlam, p1487_0]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h1378, h1448, h1478, h1479, h1480, h1484, h1486, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1487_1, u3elo1]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h1378, hlam, p1487_0]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h0, h1378, h1479, h1484, h1486, hc05, hc45, hlam, hphi, ht0b, ht5b, p1487_1]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h1475, hlam, p1487_0]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [h1476, hlam, p1487_1]
                                      · have p1487_0 := h1487c.1
                                        have p1487_1 := h1487c.2.1
                                        have p1487_2 := h1487c.2.2.1
                                        have p1487_3 := h1487c.2.2.2
                                        linarith only [hlam, p1487_0]
                                    · linarith only [h1476, h1486, hc34, hlam, hphi, u4elo0]
                                  · linarith only [h1378, h1448, h1482, h1485, h897, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                                · linarith only [h0, h1378, h1379, h1448, h1481, h1484, hc03, hlam, hphi, ht34, u4elo2]
                              · linarith only [h0, h1378, h1379, h1479, h1483, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                            · linarith only [h0, h1378, h1448, h1478, h1479, h1482, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo4]
                          · linarith only [h0, h1378, h1448, h1478, h1479, h1480, h1481, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo4]
                        · linarith only [h1474, h1480, hc13, hlam, hphi, u3elo0]
                      · linarith only [h0, h1378, h1379, h1477, h1479, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h1378, h1379, h1477, h1478, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h1378, h1477, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h1164, h1378, h1476, hlam]
              · linarith only [h1164, h1378, h1474, h1475, hc34, hlam, hphi, u4elo1]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1525 | h1525
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1526 | h1526
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1527 | h1527
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1528 | h1528
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1529 | h1529
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1530 | h1530
                        · linarith only [h0, h1379, h1474, h1530, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h1378, h1529, h1530, h897, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u4elo3]
                      · linarith only [h0, h1379, h1527, h1529, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h1378, h1379, h1527, h1528, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h0, h1378, h1527, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · linarith only [h0, h1378, h1379, h1474, h1526, hlam]
              · linarith only [h0, h1378, h1379, h1525, hlam]
      · rcases m.htr 0 2 3 (by decide) (by decide) with h1538 | h1538
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1539 | h1539
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1540 | h1540
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1541 | h1541
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1542 | h1542
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1543 | h1543
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1544 | h1544
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1545 | h1545
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1546 | h1546
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1547 | h1547
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1548 | h1548
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1549 | h1549
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1550 | h1550
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1551 | h1551
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1552 | h1552
                                    · rcases h0bigk with h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c | h1553c
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [hlam, p1553_0]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [h0, hlam, p1553_1]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [h897, hlam, p1553_0]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [h1164, hlam, p1553_1]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [h1378, hlam, p1553_1]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [h0, hc01, hc12, hlam, hphi, p1553_1]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [hlam, p1553_0]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [h0, h1538, h1549, h1552, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1553_1]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [h0, h1164, hc01, hc12, hlam, hphi, p1553_1]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [h0, h1378, hc01, hc12, hlam, hphi, p1553_1]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [h897, hc01, hc13, hlam, hphi, p1553_1]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [h1538, hlam, p1553_1]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [hlam, p1553_0]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [h1539, h1549, h1552, h897, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1553_1, u3elo1]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [h1378, h897, hc01, hlam, hphi, ht12, ht23, p1553_1, u3elo1]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p1553_1, u4elo0]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [h1539, hlam, p1553_0]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [h1540, hlam, p1553_0]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [hlam, p1553_0]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [h1164, h1378, hc01, hlam, hphi, ht12, ht23, ht34, p1553_1, u4elo1]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [h1378, hc01, hc15, hlam, hphi, p1553_1]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [h1164, h1542, hc02, hlam, hphi, ht23, ht34, p1553_1, u4elo1]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [h1541, hlam, p1553_0]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [h1542, hlam, p1553_1]
                                      · have p1553_0 := h1553c.1
                                        have p1553_1 := h1553c.2.1
                                        have p1553_2 := h1553c.2.2.1
                                        have p1553_3 := h1553c.2.2.2
                                        linarith only [hlam, p1553_0]
                                    · linarith only [h1164, h1542, h1552, hc34, hlam, hphi, u4elo1]
                                  · linarith only [h1164, h1542, h1549, h1551, hc34, hlam, hphi, u4elo1]
                                · linarith only [h1541, h1550, h897, hc23, hlam, hphi, u3elo1]
                              · linarith only [h1540, h1549, h897, hc23, hlam, hphi, u3elo1]
                            · linarith only [h1164, h1542, h1548, hlam]
                          · linarith only [h1541, h1547, h897, hlam]
                        · linarith only [h1540, h1546, h897, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1586 | h1586
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1587 | h1587
                          · linarith only [h1543, h1545, h1587, hlam]
                          · linarith only [h1541, h1587, hc13, hlam, hphi, u3elo0]
                        · linarith only [h1540, h1586, h897, hlam]
                    · linarith only [h1540, h1543, h1544, h897, hc34, hlam, hphi, u4elo2]
                  · linarith only [h0, h1543, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1593 | h1593
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1594 | h1594
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1595 | h1595
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1596 | h1596
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1597 | h1597
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1598 | h1598
                            · linarith only [h1542, h1598, hc04, hlam, hphi, u4elo1]
                            · linarith only [h1164, h1598, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                          · linarith only [h1597, h897, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h1596, h897, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1603 | h1603
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1604 | h1604
                          · linarith only [h1593, h1595, h1604, hlam]
                          · linarith only [h1604, h897, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h0, h1538, h1540, h1603, h897, hc01, hc12, hlam, hphi]
                    · linarith only [h0, h1594, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1538, h1593, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1610 | h1610
                · linarith only [h1540, h1541, h1610, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1612 | h1612
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1613 | h1613
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1614 | h1614
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1615 | h1615
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1616 | h1616
                          · linarith only [h1541, h1616, hc03, hlam, hphi, u3elo1]
                          · linarith only [h1616, h897, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h1615, h897, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1620 | h1620
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1621 | h1621
                          · linarith only [h1540, h1541, h1621, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h1621, h897, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h1620, h897, hc01, hlam, hphi, ht12, ht23, u3elo3]
                    · linarith only [h0, h1613, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1612, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1627 | h1627
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1628 | h1628
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1629 | h1629
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1630 | h1630
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1631 | h1631
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1632 | h1632
                        · linarith only [h1540, h1632, hc03, hlam, hphi, u3elo1]
                        · linarith only [h1632, h897, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1635 | h1635
                        · linarith only [h1540, h1627, h1635, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                        · linarith only [h1635, h897, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h1630, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1629, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1540, h1627, h1628, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1641 | h1641
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1642 | h1642
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1643 | h1643
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1644 | h1644
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1645 | h1645
                        · linarith only [h1540, h1645, hc03, hlam, hphi, u3elo1]
                        · linarith only [h1645, h897, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1648 | h1648
                        · linarith only [h1540, h1648, h897, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h1648, h897, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h0, h1643, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1642, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1653 | h1653
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1654 | h1654
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1655 | h1655
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1656 | h1656
                        · linarith only [h1540, h1656, h897, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h1656, h897, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1659 | h1659
                        · linarith only [h1540, h1653, h1655, h1659, h897, hc01, hc25, hlam, hphi, ht12]
                        · linarith only [h1659, h897, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                    · linarith only [h1653, h1654, h897, hc01, hlam, hphi, ht12, ht23, ht34, u4elo2]
                  · linarith only [h0, h1653, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · linarith only [h1538, h1539, hc23, hlam, hphi, ht34, u4elo2]
        · rcases m.htr 0 2 4 (by decide) (by decide) with h1665 | h1665
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1666 | h1666
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1667 | h1667
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1668 | h1668
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1669 | h1669
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1670 | h1670
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1671 | h1671
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1672 | h1672
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1673 | h1673
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1674 | h1674
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1675 | h1675
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1676 | h1676
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1677 | h1677
                                  · linarith only [h1538, h1665, h1669, h1677, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h1668, h1677, hc24, hlam, hphi, u4elo0]
                                · linarith only [h1538, h1665, h1667, h1675, h1676, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                              · linarith only [h1538, h1665, h1675, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                            · linarith only [h1538, h1665, h1668, h1674, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                          · linarith only [h1538, h1665, h1667, h1668, h1669, h1673, hlam]
                        · linarith only [h1538, h1669, h1672, hc02, hlam, hphi, ht23, u3elo3]
                      · linarith only [h1538, h1665, h1669, h1671, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h1538, h1665, h1669, h1670, hlam]
                  · linarith only [h0, h1669, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1688 | h1688
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1689 | h1689
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1690 | h1690
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1691 | h1691
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1692 | h1692
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1693 | h1693
                            · linarith only [h1164, h1668, h1693, hc01, hlam, hphi, ht12, ht23, ht34, u4elo1]
                            · linarith only [h1164, h1538, h1665, h1688, h1693, hc01, hc24, hlam, hphi, ht12, ht23, u3elo1, u4elo4]
                          · linarith only [h1538, h1665, h1688, h1692, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h1538, h1665, h1688, h1691, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
                      · linarith only [h1538, h1665, h1688, h1690, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h1538, h1665, h1688, h1689, hlam]
                  · linarith only [h0, h1688, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1701 | h1701
                · linarith only [h1538, h1665, h1667, h1701, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1703 | h1703
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1704 | h1704
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1705 | h1705
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1706 | h1706
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1707 | h1707
                          · linarith only [h1538, h1665, h1667, h1707, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h1707, h897, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h1538, h1665, h1666, h1703, h1706, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h1538, h1665, h1703, h1705, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h1538, h1665, h1703, h1704, hlam]
                  · linarith only [h0, h1703, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h1538, h1665, h1666, hc24, hlam, hphi, u4elo3]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1715 | h1715
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1716 | h1716
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1717 | h1717
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1718 | h1718
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1719 | h1719
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1720 | h1720
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1721 | h1721
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1722 | h1722
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1723 | h1723
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1724 | h1724
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1725 | h1725
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1726 | h1726
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1727 | h1727
                                    · rcases h0bigk with h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c | h1728c
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [hlam, p1728_0]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [h0, hlam, p1728_1]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [h897, hlam, p1728_0]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [h1164, hlam, p1728_1]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [h1378, hlam, p1728_1]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [h1665, h1719, hc01, hlam, hphi, ht12, ht23, ht34, p1728_1, u4elo1]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [hlam, p1728_0]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [h1538, hlam, p1728_0]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [h1665, hlam, p1728_1]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [h1665, h1719, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1728_1, u4elo1]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, p1728_1, u3elo0]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [h1538, h1718, hc02, hlam, hphi, ht23, p1728_1, u3elo1]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [hlam, p1728_0]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [h0, h1538, h1665, h1718, hc01, hlam, hphi, ht12, ht23, p1728_1, u3elo1]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [h1378, h1538, h1718, hc01, hlam, hphi, ht12, ht23, p1728_1, u3elo1]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [hc01, hlam, hphi, ht12, ht23, ht34, p1728_1, u4elo0]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [h0, h1665, h1719, hc01, hlam, hphi, ht12, ht23, ht34, p1728_1, u4elo1]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [h1715, hlam, p1728_0]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [hlam, p1728_0]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [h1665, h1719, hc05, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, p1728_1, u4elo1]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [h1378, h1723, hc01, hlam, hphi, ht12, ht23, ht34, p1728_1, u4elo1]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [h0, h1665, h1717, h1719, hc01, hlam, hphi, ht12, ht23, ht34, p1728_1, u4elo1]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [h1716, hlam, p1728_0]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [h1717, hlam, p1728_1]
                                      · have p1728_0 := h1728c.1
                                        have p1728_1 := h1728c.2.1
                                        have p1728_2 := h1728c.2.2.1
                                        have p1728_3 := h1728c.2.2.2
                                        linarith only [hlam, p1728_0]
                                    · linarith only [h1665, h1717, h1719, h1727, hc34, hlam, hphi, u4elo1]
                                  · linarith only [h1665, h1717, h1726, hlam]
                                · linarith only [h0, h1538, h1725, hc01, hlam, hphi, ht12, ht23, u3elo4]
                              · linarith only [h0, h1538, h1724, hc01, hlam, hphi, ht12, ht23, u3elo3]
                            · linarith only [h1717, h1723, hc14, hlam, hphi, u4elo0]
                          · linarith only [h1716, h1722, hc13, hlam, hphi, u3elo0]
                        · linarith only [h1538, h1715, h1718, h1721, hlam]
                      · linarith only [h0, h1538, h1718, h1720, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h1538, h1718, h1719, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h1718, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1764 | h1764
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1765 | h1765
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1766 | h1766
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1767 | h1767
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1768 | h1768
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1769 | h1769
                            · linarith only [h1665, h1717, h1769, hc02, hlam, hphi, ht23, ht34, u4elo1]
                            · linarith only [h1164, h1769, hc01, hlam, hphi, ht12, ht23, ht34, u4elo4]
                          · linarith only [h1768, h897, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h1538, h1715, h1764, h1767, hlam]
                      · linarith only [h0, h1538, h1764, h1766, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h1538, h1764, h1765, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h1764, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1777 | h1777
                · linarith only [h1715, h1716, h1777, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1779 | h1779
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1780 | h1780
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1781 | h1781
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1782 | h1782
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1783 | h1783
                          · linarith only [h1715, h1716, h1783, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo1]
                          · linarith only [h1783, h897, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h0, h1538, h1779, h1782, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1538, h1779, h1781, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h1538, h1779, h1780, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h1779, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1790 | h1790
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1791 | h1791
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1792 | h1792
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1793 | h1793
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1794 | h1794
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1795 | h1795
                        · linarith only [h1715, h1790, h1795, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                        · linarith only [h1795, h897, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h0, h1538, h1792, h1794, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h1538, h1792, h1793, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h1792, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1715, h1790, h1791, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1802 | h1802
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1803 | h1803
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1804 | h1804
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1805 | h1805
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1806 | h1806
                        · linarith only [h0, h1538, h1715, h1806, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h1806, h897, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h0, h1538, h1803, h1805, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h1538, h1803, h1804, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h1803, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1812 | h1812
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1813 | h1813
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1814 | h1814
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1815 | h1815
                        · linarith only [h0, h1538, h1715, h1815, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h1815, h897, hc01, hlam, hphi, ht12, ht23, ht34, u4elo3]
                      · linarith only [h0, h1538, h1812, h1814, hc01, hc25, hlam, hphi, ht12]
                    · linarith only [h0, h1538, h1812, h1813, hc01, hc24, hlam, hphi, ht12]
                  · linarith only [h0, h1812, hc01, hlam, hphi, ht12, ht23, u3elo2]

set_option maxHeartbeats 3642000 in
set_option maxHeartbeats 3642000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_0_L_0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_0 m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h3elo := hb3.1
  have h4elo := hb4.1
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  have u4elo0 := h4elo (m.d 0 4) (by simp)
  have u4elo1 := h4elo (m.d 1 4) (by simp)
  have u4elo2 := h4elo (m.d 2 4) (by simp)
  have u4elo3 := h4elo (m.d 3 4) (by simp)
  have u4elo4 := h4elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_11_13_14_H_I_L_I_L_0_L_0_x0 m hb0 hb1 hb3 hb4 h0
  · exact r1l7_20_11_13_14_H_I_L_I_L_0_L_0_x1 m hb0 hb1 hb3 hb4 h0

end R2N4
