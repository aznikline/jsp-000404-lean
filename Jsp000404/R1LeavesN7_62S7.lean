import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_62S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 3176000 in
set_option maxHeartbeats 3176000 in
theorem r1l7_20_12_13_15_H_I_L_0_L_0_L_I_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h3elo := hb3.1
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
  rcases m.htr 0 1 3 (by decide) (by decide) with h929 | h929
  · rcases m.htr 0 1 5 (by decide) (by decide) with h930 | h930
    · rcases m.htr 0 2 3 (by decide) (by decide) with h931 | h931
      · rcases m.htr 0 2 4 (by decide) (by decide) with h932 | h932
        · rcases m.htr 0 2 5 (by decide) (by decide) with h933 | h933
          · rcases m.htr 0 3 4 (by decide) (by decide) with h934 | h934
            · rcases m.htr 0 3 5 (by decide) (by decide) with h935 | h935
              · rcases m.htr 0 4 5 (by decide) (by decide) with h936 | h936
                · rcases m.htr 1 2 3 (by decide) (by decide) with h937 | h937
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h938 | h938
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h939 | h939
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h940 | h940
                        · linarith only [h0, h929, h940, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h0, h929, h934, h937, h940, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h939, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h929, h932, h934, h938, hlam]
                  · linarith only [h0, h937, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h946 | h946
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h947 | h947
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h948 | h948
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h949 | h949
                        · linarith only [h0, h929, h949, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h0, h929, h934, h949, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h948, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h929, h932, h935, h936, h947, hlam]
                  · linarith only [h0, h946, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h955 | h955
                · linarith only [h934, h935, h955, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h957 | h957
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h958 | h958
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h959 | h959
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h960 | h960
                        · linarith only [h0, h929, h960, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h934, h935, h960, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h929, h957, h959, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h930, h932, h934, h935, h958, hlam]
                  · linarith only [h0, h957, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h966 | h966
              · rcases m.htr 0 4 5 (by decide) (by decide) with h967 | h967
                · rcases m.htr 1 2 3 (by decide) (by decide) with h968 | h968
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h969 | h969
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h970 | h970
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h971 | h971
                        · linarith only [h0, h929, h934, h971, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h973 | h973
                          · linarith only [h0, h929, h973, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h934, h966, h973, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h970, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h969, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h929, h968, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · linarith only [h934, h966, h967, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h980 | h980
                · rcases m.htr 1 2 3 (by decide) (by decide) with h981 | h981
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h982 | h982
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h983 | h983
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h984 | h984
                        · linarith only [h934, h984, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h986 | h986
                          · linarith only [h929, h966, h986, hlam]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h988 | h988
                            · linarith only [h929, h934, h981, h988, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h990 | h990
                              · linarith only [h929, h966, h981, h990, hlam]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h992 | h992
                                · rcases h0bigk with h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c | h993c
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [hlam, p993_0]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h0, hlam, p993_1]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h0, h929, h981, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p993_1, u2elo1]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h0, h980, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p993_1, u2elo1]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h0, h929, h966, h981, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p993_1, u2elo1]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p993_1, u2elo1]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [hlam, p993_0]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h0, h929, h981, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p993_1, u2elo1]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h0, h980, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p993_1, u2elo1]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h0, h929, h966, h981, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p993_1, u2elo1]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h929, hlam, p993_1]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h931, hlam, p993_1]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [hlam, p993_0]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h934, hlam, p993_1]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h966, hlam, p993_1]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h930, h981, h986, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p993_1]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h932, hlam, p993_0]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h929, h934, h981, hc23, hlam, hphi, p993_1, u3elo3]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [hlam, p993_0]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h929, h934, h966, h981, hc23, hlam, hphi, p993_1, u3elo3]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h930, hlam, p993_0]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h933, hlam, p993_1]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h0, h929, h930, h981, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p993_1, u2elo1]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [h980, hlam, p993_1]
                                  · have p993_0 := h993c.1
                                    have p993_1 := h993c.2.1
                                    have p993_2 := h993c.2.2.1
                                    have p993_3 := h993c.2.2.2
                                    linarith only [hlam, p993_0]
                                · linarith only [h934, h980, h992, hlam]
                      · linarith only [h0, h983, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h929, h981, h982, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h981, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1023 | h1023
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1024 | h1024
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1025 | h1025
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1026 | h1026
                        · linarith only [h0, h1026, h929, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1028 | h1028
                          · linarith only [h0, h1028, h929, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1030 | h1030
                            · linarith only [h0, h1023, h1028, h1030, h930, h934, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1032 | h1032
                              · linarith only [h0, h1023, h1032, h929, h966, h980, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1034 | h1034
                                · linarith only [h1023, h1034, h929, h934, h980, hc23, hlam, hphi, u3elo3]
                                · rcases h0bigk with h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [hlam, p1036_0]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [h0, hlam, p1036_1]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [h0, h1023, h929, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1036_1, u2elo1]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [h0, h1023, h929, h934, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1036_1, u2elo1]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1036_1, u2elo1]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, p1036_1, u2elo0]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [hlam, p1036_0]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [h0, h1023, h929, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1036_1, u2elo1]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [h0, h1023, h929, h934, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1036_1, u2elo1]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [h0, h1025, h930, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p1036_1, u2elo1]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [h929, hlam, p1036_1]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [h931, hlam, p1036_1]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [hlam, p1036_0]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [h934, hlam, p1036_1]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [h966, hlam, p1036_1]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [h1023, h1028, h930, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1036_1]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [h932, hlam, p1036_0]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [h1023, h929, h934, hc23, hlam, hphi, p1036_1, u3elo3]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [hlam, p1036_0]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [h980, hlam, p1036_0]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [h930, hlam, p1036_0]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [h933, hlam, p1036_1]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [h0, h1023, h929, h930, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1036_1, u2elo1]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [h0, h930, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1036_1, u2elo1]
                                  · have p1036_0 := h1036c.1
                                    have p1036_1 := h1036c.2.1
                                    have p1036_2 := h1036c.2.2.1
                                    have p1036_3 := h1036c.2.2.2
                                    linarith only [hlam, p1036_0]
                      · linarith only [h0, h1025, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h1023, h1024, h929, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1023, h929, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
          · linarith only [h0, h930, h933, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1066 | h1066
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1067 | h1067
            · linarith only [h0, h1067, h929, h932, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1069 | h1069
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1070 | h1070
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1071 | h1071
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1072 | h1072
                    · linarith only [h0, h1071, h1072, h929, h932, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1071, h1072, h929, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1071, h929, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · linarith only [h1067, h1069, h1070, h931, h932, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1077 | h1077
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1078 | h1078
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1079 | h1079
                    · linarith only [h0, h1078, h1079, h929, h932, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1078, h1079, h929, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1078, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h0, h1077, h930, h932, hlam]
          · linarith only [h0, h1066, h930, hlam]
      · linarith only [h0, h929, h931, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1086 | h1086
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1087 | h1087
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1088 | h1088
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1089 | h1089
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1090 | h1090
              · linarith only [h1090, h929, h930, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1092 | h1092
                · linarith only [h1089, h1092, h929, h930, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1094 | h1094
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1095 | h1095
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1096 | h1096
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1097 | h1097
                        · linarith only [h1096, h1097, h929, h930, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · linarith only [h1089, h1090, h1097, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h1094, h1096, h929, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h1087, h1089, h1090, h1095, hc02, hlam, hphi, ht23, u3elo4]
                  · linarith only [h0, h1094, hc01, hlam, hphi, ht12, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1103 | h1103
              · linarith only [h1103, h929, h930, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1105 | h1105
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1106 | h1106
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1107 | h1107
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1108 | h1108
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1109 | h1109
                        · linarith only [h1089, h1108, h1109, h929, h930, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1111 | h1111
                          · linarith only [h1103, h1108, h1111, h929, h930, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h1106, h1111, h929, h930, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h1088, h1108, hlam]
                    · linarith only [h0, h1087, h1107, hlam]
                  · linarith only [h0, h1106, h929, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1117 | h1117
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1118 | h1118
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1119 | h1119
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1120 | h1120
                        · linarith only [h0, h1120, h929, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1122 | h1122
                          · linarith only [h1119, h1122, h929, h930, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                          · linarith only [h1122, h929, h930, hc13, hlam, hphi, u3elo4]
                      · linarith only [h0, h1088, h1119, hlam]
                    · linarith only [h0, h1087, h1118, hlam]
                  · linarith only [h0, h1117, hc01, hlam, hphi, ht12, u2elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1128 | h1128
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1129 | h1129
              · linarith only [h1129, h929, h930, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1131 | h1131
                · linarith only [h0, h1088, h1128, h1131, h929, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1133 | h1133
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1134 | h1134
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1135 | h1135
                      · linarith only [h0, h1088, h1133, h1135, h929, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                      · linarith only [h0, h1133, h1135, h929, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h1087, h1133, h1134, h929, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h1133, h929, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1140 | h1140
              · linarith only [h1140, h929, h930, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1142 | h1142
                · linarith only [h1087, h1088, h1142, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1144 | h1144
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1145 | h1145
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1146 | h1146
                      · linarith only [h1088, h1146, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1144, h1146, h929, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                    · linarith only [h0, h1144, h1145, h929, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1144, h929, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1151 | h1151
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1152 | h1152
            · linarith only [h0, h1087, h1152, h929, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1154 | h1154
              · linarith only [h1152, h1154, h929, h930, hc13, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1156 | h1156
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1157 | h1157
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1158 | h1158
                    · linarith only [h0, h1087, h1157, h1158, h929, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1157, h1158, h929, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1157, h929, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
                · linarith only [h1087, h1151, h1156, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1163 | h1163
            · linarith only [h0, h1087, h1163, h929, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1165 | h1165
              · linarith only [h1086, h1151, h1163, h1165, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1167 | h1167
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1168 | h1168
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1169 | h1169
                    · linarith only [h0, h1087, h1168, h1169, h929, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1168, h1169, h929, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1168, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1173 | h1173
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1174 | h1174
                    · linarith only [h0, h1087, h1173, h1174, h929, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1173, h1174, h929, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                  · linarith only [h0, h1173, h929, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo2]
      · linarith only [h0, h1086, h929, hc13, hlam, hphi, u3elo2]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1179 | h1179
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1180 | h1180
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1181 | h1181
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1182 | h1182
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1183 | h1183
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1184 | h1184
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1185 | h1185
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1186 | h1186
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1187 | h1187
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1188 | h1188
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1189 | h1189
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1190 | h1190
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1191 | h1191
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1192 | h1192
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1193 | h1193
                                · linarith only [h1180, h1191, h1193, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                · rcases h0bigk with h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c | h1195c
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [hlam, p1195_0]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h0, hlam, p1195_1]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h929, hlam, p1195_0]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h1185, h1193, h929, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1195_1, u3elo1]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h1185, h1193, h929, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1195_1, u3elo1]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p1195_1, u2elo1]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [hlam, p1195_0]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h0, h1183, h1185, h1193, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1195_1, u2elo1]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h0, h1185, h1193, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1195_1, u2elo1]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h0, h1185, h1193, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1195_1, u2elo1]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h1179, h1188, h1192, h1193, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1195_1]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h1180, hlam, p1195_1]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [hlam, p1195_0]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h1185, h1193, h929, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1195_1, u3elo1]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h1185, h1193, h929, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1195_1, u3elo1]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h1179, h1188, h1192, h1193, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1195_1]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h1181, hlam, p1195_0]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h1183, hlam, p1195_0]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [hlam, p1195_0]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h1183, h1185, h1193, h929, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1195_1, u3elo1]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h1179, hlam, p1195_0]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h1182, hlam, p1195_1]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h1184, hlam, p1195_0]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [h1185, hlam, p1195_1]
                                  · have p1195_0 := h1195c.1
                                    have p1195_1 := h1195c.2.1
                                    have p1195_2 := h1195c.2.2.1
                                    have p1195_3 := h1195c.2.2.2
                                    linarith only [hlam, p1195_0]
                              · linarith only [h1184, h1192, h929, hc23, hlam, hphi, u3elo1]
                            · linarith only [h1183, h1191, h929, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1190, h929, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h1183, h1189, h929, hlam]
                      · linarith only [h0, h1188, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h1179, h1186, h1187, h929, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · linarith only [h0, h1179, h1186, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1228 | h1228
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1229 | h1229
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1230 | h1230
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1231 | h1231
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1232 | h1232
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1233 | h1233
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1234 | h1234
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1235 | h1235
                                · linarith only [h1180, h1185, h1233, h1235, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases h0bigk with h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c | h1237c
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [hlam, p1237_0]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h0, hlam, p1237_1]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h929, hlam, p1237_0]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h1181, h1233, h929, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1237_1]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h929, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p1237_1]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p1237_1, u2elo1]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [hlam, p1237_0]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1237_1, u2elo1]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h0, h1181, h1233, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1237_1, u2elo1]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h0, h1179, h1230, h1234, h1235, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1237_1, u2elo1]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h1179, h1230, h1234, h1235, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p1237_1]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h1180, hlam, p1237_1]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [hlam, p1237_0]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h1181, h1233, h929, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1237_1, u3elo1]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h1179, h1230, h1234, h1235, h929, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1237_1, u3elo1]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h1179, h1230, h1234, h1235, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p1237_1]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h1181, hlam, p1237_0]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h1183, hlam, p1237_0]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [hlam, p1237_0]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h1185, hlam, p1237_0]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h1179, hlam, p1237_0]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h1182, hlam, p1237_1]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h1184, hlam, p1237_0]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [h0, h1179, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1237_1, u2elo1]
                                  · have p1237_0 := h1237c.1
                                    have p1237_1 := h1237c.2.1
                                    have p1237_2 := h1237c.2.2.1
                                    have p1237_3 := h1237c.2.2.2
                                    linarith only [hlam, p1237_0]
                              · linarith only [h1184, h1234, h929, hc23, hlam, hphi, u3elo1]
                            · linarith only [h1183, h1233, h929, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1232, h929, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h1179, h1230, h1231, h929, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h0, h1230, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h0, h1179, h1229, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · linarith only [h0, h1179, h1228, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
              · linarith only [h1179, h1184, h929, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1271 | h1271
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1272 | h1272
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1273 | h1273
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1274 | h1274
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1275 | h1275
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1276 | h1276
                        · linarith only [h1183, h1273, h1276, h929, hc01, hlam, hphi, ht12, u2elo1]
                        · linarith only [h1179, h1275, h1276, h929, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
                      · linarith only [h0, h1275, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h1179, h1273, h1274, h929, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo3]
                  · linarith only [h1180, h1273, hc12, hlam, hphi, u2elo0]
                · linarith only [h1179, h1183, h1272, h929, hlam]
              · linarith only [h1179, h1271, h929, hlam]
          · linarith only [h1179, h1180, h1182, h929, hc23, hlam, hphi, u3elo1]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1285 | h1285
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1286 | h1286
            · linarith only [h1180, h1181, h1286, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1288 | h1288
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1289 | h1289
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1290 | h1290
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1291 | h1291
                    · linarith only [h1180, h1181, h1291, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1291, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1179, h1180, h1290, hc02, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h1179, h1181, h1289, hlam]
              · linarith only [h1179, h1288, h929, hlam]
          · linarith only [h1179, h1180, h1285, h929, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1298 | h1298
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1299 | h1299
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1300 | h1300
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1301 | h1301
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1302 | h1302
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1303 | h1303
                  · linarith only [h1180, h1303, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1303, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1306 | h1306
                  · linarith only [h1180, h1298, h1306, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1179, h1306, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
              · linarith only [h0, h1179, h1180, h1301, hlam]
            · linarith only [h1180, h1298, h1300, hlam]
          · linarith only [h0, h1179, h1299, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1312 | h1312
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1313 | h1313
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1314 | h1314
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1315 | h1315
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1316 | h1316
                  · linarith only [h1180, h1312, h1316, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · linarith only [h0, h1179, h1316, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h0, h1179, h1298, h1315, hlam]
              · linarith only [h0, h1179, h1298, h1313, h1314, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1321 | h1321
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1322 | h1322
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1323 | h1323
                  · linarith only [h0, h1179, h1180, h1323, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo1]
                  · linarith only [h0, h1179, h1323, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · linarith only [h1179, h1313, h1322, h929, hlam]
              · linarith only [h0, h1179, h1180, h1321, hlam]
          · linarith only [h0, h1179, h1312, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1329 | h1329
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1330 | h1330
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1331 | h1331
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1332 | h1332
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1333 | h1333
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1334 | h1334
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1335 | h1335
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1336 | h1336
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1337 | h1337
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1338 | h1338
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1339 | h1339
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1340 | h1340
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1341 | h1341
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1342 | h1342
                                · linarith only [h1329, h1340, h1342, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo0]
                                · rcases h0bigk with h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c | h1344c
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [hlam, p1344_0]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [h0, hlam, p1344_1]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [h929, hlam, p1344_0]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [h1179, h1334, h1335, h1339, h1342, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1344_1, u2elo1]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [h1179, hlam, p1344_1]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p1344_1, u2elo1]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [hlam, p1344_0]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1344_1, u2elo1]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [h0, h1334, h1342, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1344_1, u2elo1]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [h0, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1344_1, u2elo1]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, ht23, p1344_1, u3elo0]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [h1329, hlam, p1344_1]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [hlam, p1344_0]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [h1334, h1342, h929, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1344_1, u3elo1]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [h1179, h929, hc01, hlam, hphi, ht12, ht23, p1344_1, u3elo1]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [h0, h1330, hc01, hlam, hphi, ht12, p1344_1, u2elo1]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [h1330, hlam, p1344_0]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [h1332, hlam, p1344_0]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [hlam, p1344_0]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [h1332, h1334, h1342, h929, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1344_1, u3elo1]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [h1179, h1339, hc01, hlam, hphi, ht12, ht23, p1344_1, u3elo1]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [h1331, hlam, p1344_1]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [h1333, hlam, p1344_0]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [h1334, hlam, p1344_1]
                                  · have p1344_0 := h1344c.1
                                    have p1344_1 := h1344c.2.1
                                    have p1344_2 := h1344c.2.2.1
                                    have p1344_3 := h1344c.2.2.2
                                    linarith only [hlam, p1344_0]
                              · linarith only [h1333, h1341, h929, hc23, hlam, hphi, u3elo1]
                            · linarith only [h1332, h1340, h929, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1333, h1339, h929, hlam]
                        · linarith only [h1332, h1338, h929, hlam]
                      · linarith only [h0, h1331, h1337, hlam]
                    · linarith only [h0, h1336, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1335, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1377 | h1377
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1378 | h1378
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1379 | h1379
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1380 | h1380
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1381 | h1381
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h1382 | h1382
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h1383 | h1383
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h1384 | h1384
                                · linarith only [h1329, h1334, h1382, h1384, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                                · rcases h0bigk with h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c | h1386c
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h0, hlam, p1386_1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h929, hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h0, h1330, h1382, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1386_1, u2elo1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h1179, hlam, p1386_1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h0, hc01, hlam, hphi, ht12, p1386_1, u2elo1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h0, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1386_1, u2elo1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h0, h1330, h1382, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1386_1, u2elo1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h0, h1179, hc01, hlam, hphi, ht12, p1386_1, u2elo1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [hc01, hlam, hphi, ht12, ht23, p1386_1, u3elo0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h1329, hlam, p1386_1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h1330, h1382, h929, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1386_1, u3elo1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h1179, h929, hc01, hlam, hphi, ht12, ht23, p1386_1, u3elo1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h1334, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p1386_1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h1330, hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h1332, hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h1334, hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h1179, h1381, hc01, hlam, hphi, ht12, ht23, p1386_1, u3elo1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h1331, hlam, p1386_1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h1333, hlam, p1386_0]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [h1179, h1381, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1386_1, u3elo1]
                                  · have p1386_0 := h1386c.1
                                    have p1386_1 := h1386c.2.1
                                    have p1386_2 := h1386c.2.2.1
                                    have p1386_3 := h1386c.2.2.2
                                    linarith only [hlam, p1386_0]
                              · linarith only [h1333, h1383, h929, hc23, hlam, hphi, u3elo1]
                            · linarith only [h1332, h1382, h929, hc23, hlam, hphi, u3elo1]
                          · linarith only [h1333, h1381, h929, hlam]
                        · linarith only [h1332, h1380, h929, hlam]
                      · linarith only [h0, h1331, h1379, hlam]
                    · linarith only [h0, h1330, h1378, hlam]
                  · linarith only [h0, h1377, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1419 | h1419
                · linarith only [h1332, h1333, h1419, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1421 | h1421
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1422 | h1422
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1423 | h1423
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1424 | h1424
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1425 | h1425
                          · linarith only [h1332, h1333, h1421, h1425, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                          · linarith only [h1425, h929, hc01, hlam, hphi, ht12, ht23, u3elo4]
                        · linarith only [h1424, h929, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1423, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h1421, h1422, h929, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1421, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1432 | h1432
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1433 | h1433
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1434 | h1434
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1435 | h1435
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1436 | h1436
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1437 | h1437
                        · linarith only [h1332, h1432, h1437, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo1]
                        · linarith only [h1437, h929, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1436, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h1434, h1435, h929, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1329, h1434, hlam]
                · linarith only [h1332, h1432, h1433, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1444 | h1444
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1445 | h1445
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1446 | h1446
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1447 | h1447
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1448 | h1448
                        · linarith only [h1332, h1448, hc03, hlam, hphi, u3elo1]
                        · linarith only [h1448, h929, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1331, h1447, hlam]
                    · linarith only [h0, h1330, h1446, hlam]
                  · linarith only [h0, h1329, h1445, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1454 | h1454
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1455 | h1455
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1456 | h1456
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1457 | h1457
                        · linarith only [h1332, h1457, h929, hc01, hlam, hphi, ht12, ht23, u3elo1]
                        · linarith only [h1457, h929, hc01, hlam, hphi, ht12, ht23, u3elo3]
                      · linarith only [h0, h1331, h1456, hlam]
                    · linarith only [h0, h1330, h1455, hlam]
                  · linarith only [h0, h1329, h1454, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1463 | h1463
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1464 | h1464
              · linarith only [h1329, h1331, h1464, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1466 | h1466
                · linarith only [h1330, h1331, h1466, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1468 | h1468
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1469 | h1469
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1470 | h1470
                      · linarith only [h1331, h1470, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1470, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h1468, h1469, h929, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h1329, h1468, hc12, hlam, hphi, u2elo0]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1475 | h1475
              · linarith only [h1330, h1331, h1463, h1475, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1477 | h1477
                · linarith only [h1330, h1331, h1477, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1479 | h1479
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1480 | h1480
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1481 | h1481
                      · linarith only [h1331, h1481, hc02, hlam, hphi, u2elo1]
                      · linarith only [h0, h1481, hc01, hlam, hphi, ht12, u2elo4]
                    · linarith only [h1479, h1480, h929, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1479, hc01, hlam, hphi, ht12, u2elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1486 | h1486
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1487 | h1487
            · linarith only [h1329, h1330, h1487, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1489 | h1489
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1490 | h1490
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1491 | h1491
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1492 | h1492
                    · linarith only [h1330, h1492, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1492, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1491, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1329, h1330, h1487, h1489, h1490, hc23, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1497 | h1497
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1498 | h1498
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1499 | h1499
                    · linarith only [h1329, h1330, h1499, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                    · linarith only [h0, h1499, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1498, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1330, h1486, h1497, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1504 | h1504
            · linarith only [h1329, h1330, h1504, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1506 | h1506
              · linarith only [h1329, h1486, h1506, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1508 | h1508
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1509 | h1509
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1510 | h1510
                    · linarith only [h1330, h1510, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1510, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1509, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1514 | h1514
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1515 | h1515
                    · linarith only [h1330, h1515, hc02, hlam, hphi, u2elo1]
                    · linarith only [h0, h1515, hc01, hlam, hphi, ht12, u2elo3]
                  · linarith only [h0, h1514, hc01, hlam, hphi, ht12, u2elo2]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1519 | h1519
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1520 | h1520
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1521 | h1521
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1522 | h1522
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1523 | h1523
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1524 | h1524
                  · linarith only [h1329, h1524, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1524, hc01, hlam, hphi, ht12, u2elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1527 | h1527
                  · linarith only [h1329, h1527, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1527, hc01, hlam, hphi, ht12, u2elo2]
              · linarith only [h1329, h1520, h1522, hlam]
            · linarith only [h1329, h1519, h1521, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1532 | h1532
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1533 | h1533
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1534 | h1534
                · linarith only [h1519, h1520, h1534, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1536 | h1536
                  · linarith only [h1329, h1519, h1536, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1536, hc01, hlam, hphi, ht12, ht23, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1539 | h1539
                · linarith only [h1329, h1519, h1533, h1539, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1541 | h1541
                  · linarith only [h1329, h1519, h1541, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo1]
                  · linarith only [h0, h1541, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · linarith only [h1329, h1519, h1532, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1545 | h1545
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1546 | h1546
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1547 | h1547
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1548 | h1548
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1549 | h1549
                  · linarith only [h1329, h1549, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1549, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1519, h1545, h1548, hlam]
              · linarith only [h1329, h1545, h1547, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1554 | h1554
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1555 | h1555
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1556 | h1556
                  · linarith only [h1329, h1556, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1556, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1329, h1545, h1546, h1555, hlam]
              · linarith only [h1329, h1545, h1554, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1561 | h1561
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1562 | h1562
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1563 | h1563
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1564 | h1564
                  · linarith only [h1329, h1564, hc02, hlam, hphi, u2elo1]
                  · linarith only [h0, h1564, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1567 | h1567
                  · linarith only [h0, h1329, h1567, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1567, hc01, hlam, hphi, ht12, u2elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1570 | h1570
                · linarith only [h1561, h1562, h1570, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1572 | h1572
                  · linarith only [h0, h1329, h1572, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1572, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1575 | h1575
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1576 | h1576
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1577 | h1577
                  · linarith only [h0, h1329, h1577, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1577, hc01, hlam, hphi, ht12, u2elo2]
                · linarith only [h1561, h1575, h1576, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1581 | h1581
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1582 | h1582
                  · linarith only [h0, h1329, h1582, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1582, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1585 | h1585
                  · linarith only [h0, h1329, h1585, hc01, hlam, hphi, ht12, u2elo1]
                  · linarith only [h0, h1585, hc01, hlam, hphi, ht12, u2elo2]

set_option maxHeartbeats 3176000 in
set_option maxHeartbeats 3176000 in
theorem r1l7_20_12_13_15_H_I_L_0_L_0_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
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
  have h0bigk := hb0.1
  have h2elo := hb2.1
  have h3elo := hb3.1
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
  · exact r1l7_20_12_13_15_H_I_L_0_L_0_L_I_x0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_H_I_L_0_L_0_L_I_x1 m hb0 hb2 hb3 hb5 h0

end R2N4
