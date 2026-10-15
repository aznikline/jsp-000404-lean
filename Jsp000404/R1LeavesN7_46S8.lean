import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6014000 in
set_option maxHeartbeats 6014000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_0_L_I_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_0 m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h966 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3elo := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h967 | h967
  · rcases m.htr 0 1 5 (by decide) (by decide) with h968 | h968
    · rcases m.htr 0 2 3 (by decide) (by decide) with h969 | h969
      · rcases m.htr 0 2 4 (by decide) (by decide) with h970 | h970
        · rcases m.htr 0 2 5 (by decide) (by decide) with h971 | h971
          · rcases m.htr 0 3 4 (by decide) (by decide) with h972 | h972
            · rcases m.htr 0 3 5 (by decide) (by decide) with h973 | h973
              · rcases m.htr 0 4 5 (by decide) (by decide) with h974 | h974
                · rcases m.htr 1 2 3 (by decide) (by decide) with h975 | h975
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h976 | h976
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h977 | h977
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h978 | h978
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h979 | h979
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h980 | h980
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h981 | h981
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h982 | h982
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h983 | h983
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h984 | h984
                                    · linarith only [h966, h975, h981, h984, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                    · linarith only [h0, h966, h978, h980, h984, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · linarith only [h0, h966, h978, h980, h983, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                · linarith only [h973, h982, hc23, hlam, hphi, u3elo0]
                              · linarith only [h972, h981, hc23, hlam, hphi, u3elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h990 | h990
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h991 | h991
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h992 | h992
                                  · linarith only [h970, h980, h992, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h994 | h994
                                    · linarith only [h976, h980, h990, h994, hlam]
                                    · rcases h0bigk with h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c | h996c
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [hlam, p996_0]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h0, hlam, p996_1]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h0, h969, h991, h994, hc34, hlam, hphi, ht0b, ht45, ht5b, p996_1, u0elo1]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h0, h974, h976, h980, h990, hc34, hlam, hphi, ht0b, ht45, ht5b, p996_1, u0elo1]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h0, h974, h976, h980, h990, hc34, hlam, hphi, ht0b, ht45, ht5b, p996_1, u0elo1]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h966, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p996_1, u0elo1]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [hlam, p996_0]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h972, h974, h976, h980, h990, hc34, hlam, hphi, ht0b, ht45, ht5b, p996_1, u0elo1]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h974, h976, h980, h990, hc34, hlam, hphi, ht0b, ht45, ht5b, p996_1, u0elo1]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h974, h976, h980, h990, hc34, hlam, hphi, ht0b, ht45, ht5b, p996_1, u0elo1]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h966, hlam, p996_1]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h969, hlam, p996_1]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [hlam, p996_0]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h974, h976, h980, h990, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p996_1, u3elo0]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h974, h976, h980, h990, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p996_1, u3elo0]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h967, hlam, p996_0]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h970, hlam, p996_0]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h972, hlam, p996_0]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [hlam, p996_0]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h974, h976, h980, h990, hc34, hlam, hphi, ht0b, ht45, ht5b, p996_1, u0elo3]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h968, hlam, p996_0]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h971, hlam, p996_1]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h973, hlam, p996_0]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [h974, hlam, p996_1]
                                      · have p996_0 := h996c.1
                                        have p996_1 := h996c.2.1
                                        have p996_2 := h996c.2.2.1
                                        have p996_3 := h996c.2.2.2
                                        linarith only [hlam, p996_0]
                                · linarith only [h973, h990, h991, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo0]
                              · linarith only [h972, h990, hc23, hlam, hphi, u3elo0]
                          · linarith only [h973, h979, hc13, hlam, hphi, u3elo0]
                        · linarith only [h972, h975, h978, hc23, hlam, hphi, u3elo0]
                      · linarith only [h0, h971, h977, hlam]
                    · linarith only [h0, h970, h976, hlam]
                  · linarith only [h0, h975, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1029 | h1029
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1030 | h1030
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1031 | h1031
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1032 | h1032
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1033 | h1033
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1034 | h1034
                            · linarith only [h1034, h967, h974, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1036 | h1036
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1037 | h1037
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1038 | h1038
                                  · linarith only [h1030, h1034, h1038, h968, h974, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1040 | h1040
                                    · linarith only [h1036, h1040, h970, h974, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                                    · rcases h0bigk with h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c | h1042c
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        linarith only [hlam, p1042_0]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        linarith only [h0, hlam, p1042_1]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        linarith only [h0, h1029, h1037, h1040, h966, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1042_1]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        rcases p1042_3 (m.d 0 1) (by simp) with h1046 | h1046
                                        · rcases p1042_3 (m.d 0 2) (by simp) with h1047 | h1047
                                          · rcases p1042_3 (m.d 0 3) (by simp) with h1048 | h1048
                                            · linarith only [h1048, h966, hlam]
                                            · linarith only [h1048, h972, hlam]
                                          · linarith only [h1047, h970, hlam]
                                        · linarith only [h1046, h967, hlam]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        rcases p1042_3 (m.d 0 1) (by simp) with h1053 | h1053
                                        · rcases p1042_3 (m.d 0 2) (by simp) with h1054 | h1054
                                          · rcases p1042_3 (m.d 0 3) (by simp) with h1055 | h1055
                                            · linarith only [h1055, h966, hlam]
                                            · linarith only [h1055, h973, hlam]
                                          · linarith only [h1054, h971, hlam]
                                        · linarith only [h1053, h968, hlam]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        linarith only [h1029, h1037, h1040, h966, hc34, hlam, hphi, ht0b, ht45, ht5b, p1042_1, u0elo1]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        linarith only [hlam, p1042_0]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        linarith only [h1029, h1037, h1040, h966, hc34, hlam, hphi, ht0b, ht45, ht5b, p1042_1, u0elo1]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        rcases p1042_3 (m.d 0 1) (by simp) with h1063 | h1063
                                        · linarith only [h0, h1063, hlam]
                                        · linarith only [h1063, h967, hlam]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        rcases p1042_3 (m.d 0 1) (by simp) with h1066 | h1066
                                        · linarith only [h0, h1066, hlam]
                                        · linarith only [h1066, h968, hlam]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        linarith only [h966, hlam, p1042_1]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        linarith only [h969, hlam, p1042_1]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        linarith only [hlam, p1042_0]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        rcases p1042_3 (m.d 0 1) (by simp) with h1072 | h1072
                                        · rcases p1042_3 (m.d 0 2) (by simp) with h1073 | h1073
                                          · rcases p1042_3 (m.d 0 3) (by simp) with h1074 | h1074
                                            · rcases p1042_3 (m.d 0 4) (by simp) with h1075 | h1075
                                              · linarith only [h1075, h972, hlam]
                                              · rcases p1042_3 (m.d 0 5) (by simp) with h1077 | h1077
                                                · linarith only [h1077, h973, hlam]
                                                · linarith only [h1077, h974, hlam]
                                            · linarith only [h1074, h972, hlam]
                                          · linarith only [h1073, h970, hlam]
                                        · linarith only [h1072, h967, hlam]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        rcases p1042_3 (m.d 0 1) (by simp) with h1083 | h1083
                                        · rcases p1042_3 (m.d 0 2) (by simp) with h1084 | h1084
                                          · rcases p1042_3 (m.d 0 3) (by simp) with h1085 | h1085
                                            · rcases p1042_3 (m.d 0 4) (by simp) with h1086 | h1086
                                              · linarith only [h1086, h972, hlam]
                                              · rcases p1042_3 (m.d 0 5) (by simp) with h1088 | h1088
                                                · linarith only [h1088, h973, hlam]
                                                · rcases h2bigk with h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [hlam, p1090_0]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [h0, hlam, p1090_1]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [h1037, h1040, hc34, hlam, hphi, ht0b, ht45, ht5b, p1090_1, u0elo1]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    rcases p1090_3 (m.d 0 2) (by simp) with h1094 | h1094
                                                    · rcases p1090_3 (m.d 1 2) (by simp) with h1095 | h1095
                                                      · rcases p1090_3 (m.d 2 3) (by simp) with h1096 | h1096
                                                        · linarith only [h1096, h969, hlam]
                                                        · linarith only [h1036, h1096, hlam]
                                                      · linarith only [h1030, h1095, hlam]
                                                    · linarith only [h1094, hlam, p1090_0]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    rcases p1090_3 (m.d 0 2) (by simp) with h1101 | h1101
                                                    · rcases p1090_3 (m.d 1 2) (by simp) with h1102 | h1102
                                                      · rcases p1090_3 (m.d 2 3) (by simp) with h1103 | h1103
                                                        · linarith only [h1103, h969, hlam]
                                                        · linarith only [h1037, h1103, hlam]
                                                      · linarith only [h1031, h1102, hlam]
                                                    · linarith only [h1101, hlam, p1090_0]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [h0, h1030, h1036, h966, h967, h974, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1042_1, p1090_1]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [hlam, p1090_0]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    rcases p1090_3 (m.d 0 2) (by simp) with h1110 | h1110
                                                    · linarith only [h0, h1110, hlam]
                                                    · linarith only [h1110, h969, hlam]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [h0, h1030, h966, h967, h974, hlam, p1042_1, p1090_2]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [h0, h966, h971, hlam, p1042_1, p1090_2]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [h969, hlam, p1090_0]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [h1029, hlam, p1090_0]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [hlam, p1090_0]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [h1029, h1036, h966, hc34, hlam, hphi, ht0b, ht45, ht5b, p1090_1, u0elo0]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [h0, h1029, h966, hc25, hlam, hphi, ht0b, ht5b, p1090_1, u0elo1]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [h970, hlam, p1090_0]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [h1030, hlam, p1090_0]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [h1036, hlam, p1090_1]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [hlam, p1090_0]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [h1038, hlam, p1090_1]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [h971, hlam, p1090_0]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [h1031, hlam, p1090_0]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [h1037, hlam, p1090_1]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [h1036, h971, hc34, hlam, hphi, ht0b, ht45, ht5b, p1090_1, u0elo1]
                                                  · have p1090_0 := h1090c.1
                                                    have p1090_1 := h1090c.2.1
                                                    have p1090_2 := h1090c.2.2.1
                                                    have p1090_3 := h1090c.2.2.2
                                                    linarith only [hlam, p1090_0]
                                            · linarith only [h1085, h973, hlam]
                                          · linarith only [h1084, h971, hlam]
                                        · linarith only [h1083, h968, hlam]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        linarith only [h967, hlam, p1042_0]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        linarith only [h970, hlam, p1042_0]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        linarith only [h972, hlam, p1042_0]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        linarith only [hlam, p1042_0]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        linarith only [h974, hlam, p1042_0]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        linarith only [h968, hlam, p1042_0]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        linarith only [h971, hlam, p1042_1]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        linarith only [h973, hlam, p1042_0]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        rcases p1042_3 (m.d 0 1) (by simp) with h1141 | h1141
                                        · rcases p1042_3 (m.d 0 2) (by simp) with h1142 | h1142
                                          · rcases p1042_3 (m.d 0 3) (by simp) with h1143 | h1143
                                            · rcases p1042_3 (m.d 0 4) (by simp) with h1144 | h1144
                                              · linarith only [h1144, h974, hlam]
                                              · rcases p1042_3 (m.d 0 5) (by simp) with h1146 | h1146
                                                · rcases h2bigk with h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c | h1147c
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [hlam, p1147_0]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [h0, hlam, p1147_1]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [h1036, hc34, hlam, hphi, ht0b, ht45, ht5b, p1147_1, u0elo1]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    rcases p1147_3 (m.d 0 2) (by simp) with h1151 | h1151
                                                    · rcases p1147_3 (m.d 1 2) (by simp) with h1152 | h1152
                                                      · rcases p1147_3 (m.d 2 3) (by simp) with h1153 | h1153
                                                        · linarith only [h1153, h969, hlam]
                                                        · linarith only [h1036, h1153, hlam]
                                                      · linarith only [h1030, h1152, hlam]
                                                    · linarith only [h1151, hlam, p1147_0]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    rcases p1147_3 (m.d 0 2) (by simp) with h1158 | h1158
                                                    · rcases p1147_3 (m.d 1 2) (by simp) with h1159 | h1159
                                                      · rcases p1147_3 (m.d 2 3) (by simp) with h1160 | h1160
                                                        · linarith only [h1160, h969, hlam]
                                                        · linarith only [h1037, h1160, hlam]
                                                      · linarith only [h1031, h1159, hlam]
                                                    · linarith only [h1158, hlam, p1147_0]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [h0, h1030, h1036, h967, h968, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1042_1, p1147_1]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [hlam, p1147_0]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    rcases p1147_3 (m.d 0 2) (by simp) with h1167 | h1167
                                                    · linarith only [h0, h1167, hlam]
                                                    · linarith only [h1167, h969, hlam]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [h0, h1030, h966, h967, h973, hlam, p1042_1, p1147_2]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    rcases p1147_3 (m.d 0 2) (by simp) with h1171 | h1171
                                                    · linarith only [h0, h1171, hlam]
                                                    · linarith only [h1171, h971, hlam]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [h969, hlam, p1147_0]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [h1029, hlam, p1147_0]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [hlam, p1147_0]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [h1036, h969, hc34, hlam, hphi, ht0b, ht45, ht5b, p1147_1, u0elo1]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [h1029, h966, hc25, hlam, hphi, ht0b, ht5b, p1147_1, u0elo0]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [h970, hlam, p1147_0]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [h1030, hlam, p1147_0]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [h1036, hlam, p1147_1]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [hlam, p1147_0]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [h1038, hlam, p1147_1]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [h971, hlam, p1147_0]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [h1031, hlam, p1147_0]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [h1037, hlam, p1147_1]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [h1036, h971, hc34, hlam, hphi, ht0b, ht45, ht5b, p1147_1, u0elo1]
                                                  · have p1147_0 := h1147c.1
                                                    have p1147_1 := h1147c.2.1
                                                    have p1147_2 := h1147c.2.2.1
                                                    have p1147_3 := h1147c.2.2.2
                                                    linarith only [hlam, p1147_0]
                                                · linarith only [h1146, h974, hlam]
                                            · linarith only [h1143, h972, hlam]
                                          · linarith only [h1142, h970, hlam]
                                        · linarith only [h1141, h967, hlam]
                                      · have p1042_0 := h1042c.1
                                        have p1042_1 := h1042c.2.1
                                        have p1042_2 := h1042c.2.2.1
                                        have p1042_3 := h1042c.2.2.2
                                        linarith only [hlam, p1042_0]
                                · linarith only [h1037, h973, hc23, hlam, hphi, u3elo0]
                              · linarith only [h1036, h972, hc23, hlam, hphi, u3elo0]
                          · linarith only [h1033, h973, hc13, hlam, hphi, u3elo0]
                        · linarith only [h1029, h1032, h972, hc23, hlam, hphi, u3elo0]
                      · linarith only [h0, h1031, h971, hlam]
                    · linarith only [h0, h1030, h970, hlam]
                  · linarith only [h0, h1029, h966, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1201 | h1201
                · linarith only [h1201, h972, h973, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1203 | h1203
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1204 | h1204
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1205 | h1205
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1206 | h1206
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1207 | h1207
                          · linarith only [h1207, h966, h973, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1209 | h1209
                            · linarith only [h1201, h1209, h967, hlam]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1211 | h1211
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1212 | h1212
                                · linarith only [h1203, h1212, h966, h973, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1214 | h1214
                                  · linarith only [h1201, h1204, h1214, h967, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1216 | h1216
                                    · linarith only [h1201, h1203, h1211, h1216, h966, h973, hc04, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                                    · rcases h0bigk with h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h0, hlam, p1218_1]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h0, h972, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1218_1]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        rcases p1218_3 (m.d 0 1) (by simp) with h1222 | h1222
                                        · rcases p1218_3 (m.d 0 2) (by simp) with h1223 | h1223
                                          · rcases p1218_3 (m.d 0 3) (by simp) with h1224 | h1224
                                            · linarith only [h1224, h966, hlam]
                                            · linarith only [h1224, h972, hlam]
                                          · linarith only [h1223, h970, hlam]
                                        · linarith only [h1222, h967, hlam]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h0, h1203, h1211, h966, h973, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1218_1]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h1203, h1211, h966, hc34, hlam, hphi, ht0b, ht45, ht5b, p1218_1, u0elo1]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h1203, h1211, h966, hc34, hlam, hphi, ht0b, ht45, ht5b, p1218_1, u0elo1]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        rcases p1218_3 (m.d 0 1) (by simp) with h1233 | h1233
                                        · linarith only [h0, h1233, hlam]
                                        · linarith only [h1233, h967, hlam]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h1203, h1211, h966, h973, hc34, hlam, hphi, ht0b, ht45, ht5b, p1218_1, u0elo1]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h966, hlam, p1218_1]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h969, hlam, p1218_1]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h1204, h1211, h967, h973, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1218_1, u3elo4]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h973, hlam, p1218_1]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h967, hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h970, hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h972, hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h1201, hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h968, hlam, p1218_0]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h971, hlam, p1218_1]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [h1203, h1211, h966, hc34, hlam, hphi, ht0b, ht45, ht5b, p1218_1, u0elo4]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        rcases p1218_3 (m.d 0 1) (by simp) with h1250 | h1250
                                        · rcases p1218_3 (m.d 0 2) (by simp) with h1251 | h1251
                                          · rcases p1218_3 (m.d 0 3) (by simp) with h1252 | h1252
                                            · linarith only [h1252, h973, hlam]
                                            · linarith only [h1252, h972, hlam]
                                          · linarith only [h1251, h970, hlam]
                                        · linarith only [h1250, h967, hlam]
                                      · have p1218_0 := h1218c.1
                                        have p1218_1 := h1218c.2.1
                                        have p1218_2 := h1218c.2.2.1
                                        have p1218_3 := h1218c.2.2.2
                                        linarith only [hlam, p1218_0]
                              · linarith only [h1211, h972, hc23, hlam, hphi, u3elo0]
                        · linarith only [h1203, h1206, h972, h973, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h1205, h971, hlam]
                    · linarith only [h0, h1204, h970, hlam]
                  · linarith only [h0, h1203, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1263 | h1263
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1264 | h1264
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1265 | h1265
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1266 | h1266
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1267 | h1267
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1268 | h1268
                        · linarith only [h1268, h972, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1270 | h1270
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1271 | h1271
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1272 | h1272
                              · linarith only [h1265, h1272, h966, h972, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1274 | h1274
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1275 | h1275
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1276 | h1276
                                    · rcases h0bigk with h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c | h1277c
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [hlam, p1277_0]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [h0, hlam, p1277_1]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [h1265, h1274, h1276, h966, hc45, hlam, hphi, ht0b, ht5b, p1277_1, u0elo0]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [h0, h1265, h1268, h1274, h1276, h967, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1277_1]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        rcases p1277_3 (m.d 0 1) (by simp) with h1282 | h1282
                                        · rcases p1277_3 (m.d 0 2) (by simp) with h1283 | h1283
                                          · rcases p1277_3 (m.d 0 3) (by simp) with h1284 | h1284
                                            · linarith only [h1284, h966, hlam]
                                            · linarith only [h1263, h1284, hlam]
                                          · linarith only [h1283, h971, hlam]
                                        · linarith only [h1282, h968, hlam]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [h1265, h1274, h1276, h966, hc45, hlam, hphi, ht0b, ht5b, p1277_1, u0elo1]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [hlam, p1277_0]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [h1265, h1274, h1276, h966, hc45, hlam, hphi, ht0b, ht5b, p1277_1, u0elo1]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [h1265, h1268, h1274, h1276, h967, hc45, hlam, hphi, ht0b, ht5b, p1277_1, u0elo1]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        rcases p1277_3 (m.d 0 1) (by simp) with h1293 | h1293
                                        · linarith only [h0, h1293, hlam]
                                        · linarith only [h1293, h968, hlam]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [h966, hlam, p1277_1]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [h969, hlam, p1277_1]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [hlam, p1277_0]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [h972, hlam, p1277_1]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [h1267, h1274, h1276, h968, h972, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1277_1, u3elo3]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [h967, hlam, p1277_0]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [h970, hlam, p1277_0]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [h1265, h1274, h1276, h966, hc45, hlam, hphi, ht0b, ht5b, p1277_1, u0elo3]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [hlam, p1277_0]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        rcases p1277_3 (m.d 0 1) (by simp) with h1305 | h1305
                                        · rcases p1277_3 (m.d 0 2) (by simp) with h1306 | h1306
                                          · rcases p1277_3 (m.d 0 3) (by simp) with h1307 | h1307
                                            · linarith only [h1307, h972, hlam]
                                            · linarith only [h1263, h1307, hlam]
                                          · linarith only [h1306, h971, hlam]
                                        · linarith only [h1305, h968, hlam]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [h968, hlam, p1277_0]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [h971, hlam, p1277_1]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [h1263, hlam, p1277_0]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [h1264, hlam, p1277_1]
                                      · have p1277_0 := h1277c.1
                                        have p1277_1 := h1277c.2.1
                                        have p1277_2 := h1277c.2.2.1
                                        have p1277_3 := h1277c.2.2.2
                                        linarith only [hlam, p1277_0]
                                    · linarith only [h1264, h1276, h972, hlam]
                                  · linarith only [h0, h1271, h1275, h967, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h1263, h1274, h972, hc23, hlam, hphi, u3elo3]
                            · linarith only [h1263, h1264, h1268, h1271, h972, hc13, hlam, hphi, u3elo3]
                          · linarith only [h1263, h1265, h1270, h972, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h1267, h971, hlam]
                    · linarith only [h0, h1266, h970, hlam]
                  · linarith only [h0, h1265, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1263, h1264, h972, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1326 | h1326
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1327 | h1327
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1328 | h1328
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1329 | h1329
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1330 | h1330
                        · linarith only [h1330, h972, hc03, hlam, hphi, u3elo1]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1332 | h1332
                          · linarith only [h1263, h1332, h966, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1334 | h1334
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1335 | h1335
                              · linarith only [h1327, h1332, h1334, h1335, h967, h972, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1337 | h1337
                                · linarith only [h1263, h1327, h1337, h966, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1339 | h1339
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1340 | h1340
                                    · rcases h0bigk with h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c | h1341c
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [hlam, p1341_0]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [h0, hlam, p1341_1]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        rcases p1341_3 (m.d 0 1) (by simp) with h1344 | h1344
                                        · rcases p1341_3 (m.d 0 2) (by simp) with h1345 | h1345
                                          · rcases p1341_3 (m.d 0 3) (by simp) with h1346 | h1346
                                            · linarith only [h1346, h966, hlam]
                                            · rcases p1341_3 (m.d 0 4) (by simp) with h1348 | h1348
                                              · linarith only [h1348, h967, hlam]
                                              · linarith only [h1348, h972, hlam]
                                          · linarith only [h1345, h969, hlam]
                                        · linarith only [h1344, h966, hlam]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [h0, h1328, h1339, h967, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1341_1]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        rcases p1341_3 (m.d 0 1) (by simp) with h1354 | h1354
                                        · rcases p1341_3 (m.d 0 2) (by simp) with h1355 | h1355
                                          · rcases p1341_3 (m.d 0 3) (by simp) with h1356 | h1356
                                            · linarith only [h1356, h966, hlam]
                                            · rcases p1341_3 (m.d 0 4) (by simp) with h1358 | h1358
                                              · linarith only [h1358, h967, hlam]
                                              · linarith only [h1326, h1358, hlam]
                                          · linarith only [h1355, h971, hlam]
                                        · linarith only [h1354, h968, hlam]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [h1327, h966, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1341_1, u0elo1]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [hlam, p1341_0]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        rcases p1341_3 (m.d 0 1) (by simp) with h1365 | h1365
                                        · linarith only [h0, h1365, hlam]
                                        · linarith only [h1365, h966, hlam]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [h1328, h1339, h967, hc45, hlam, hphi, ht0b, ht5b, p1341_1, u0elo1]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        rcases p1341_3 (m.d 0 1) (by simp) with h1369 | h1369
                                        · linarith only [h0, h1369, hlam]
                                        · linarith only [h1369, h968, hlam]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [h966, hlam, p1341_1]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [h969, hlam, p1341_1]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [hlam, p1341_0]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [h972, hlam, p1341_1]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [h1263, hlam, p1341_1]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [h967, hlam, p1341_0]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [h970, hlam, p1341_0]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [h1327, h966, h972, hc23, hlam, hphi, p1341_1, u3elo3]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [hlam, p1341_0]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [h1263, h1327, h966, h972, hc23, hlam, hphi, p1341_1, u3elo3]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [h968, hlam, p1341_0]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [h971, hlam, p1341_1]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [h1263, h1327, h966, hc23, hlam, hphi, p1341_1, u3elo4]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [h1326, hlam, p1341_1]
                                      · have p1341_0 := h1341c.1
                                        have p1341_1 := h1341c.2.1
                                        have p1341_2 := h1341c.2.2.1
                                        have p1341_3 := h1341c.2.2.2
                                        linarith only [hlam, p1341_0]
                                    · linarith only [h1326, h1340, h972, hlam]
                                  · linarith only [h0, h1334, h1339, h967, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                            · linarith only [h1326, h1327, h1330, h1334, h972, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h1329, h971, hlam]
                    · linarith only [h0, h1328, h970, hlam]
                  · linarith only [h0, h1327, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1393 | h1393
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1394 | h1394
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1395 | h1395
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1396 | h1396
                        · linarith only [h1396, h966, h972, hlam]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1398 | h1398
                          · linarith only [h1263, h1398, h966, hlam]
                          · rcases m.htr 1 4 5 (by decide) (by decide) with h1400 | h1400
                            · linarith only [h0, h1326, h1400, h967, h972, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 4 (by decide) (by decide) with h1402 | h1402
                              · linarith only [h1393, h1402, h966, h972, hlam]
                              · rcases m.htr 2 3 5 (by decide) (by decide) with h1404 | h1404
                                · linarith only [h1263, h1393, h1404, h966, hlam]
                                · rcases m.htr 2 4 5 (by decide) (by decide) with h1406 | h1406
                                  · linarith only [h1326, h1394, h1406, h967, hlam]
                                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1408 | h1408
                                    · linarith only [h1326, h1393, h1408, h966, h972, hc23, hlam, hphi, u3elo3]
                                    · rcases h0bigk with h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c | h1410c
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        linarith only [hlam, p1410_0]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        linarith only [h0, hlam, p1410_1]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        rcases p1410_3 (m.d 0 1) (by simp) with h1413 | h1413
                                        · rcases p1410_3 (m.d 0 2) (by simp) with h1414 | h1414
                                          · rcases p1410_3 (m.d 0 3) (by simp) with h1415 | h1415
                                            · linarith only [h1415, h966, hlam]
                                            · rcases p1410_3 (m.d 0 4) (by simp) with h1417 | h1417
                                              · linarith only [h1417, h967, hlam]
                                              · linarith only [h1417, h972, hlam]
                                          · linarith only [h1414, h969, hlam]
                                        · linarith only [h1413, h966, hlam]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        rcases p1410_3 (m.d 0 1) (by simp) with h1422 | h1422
                                        · rcases p1410_3 (m.d 0 2) (by simp) with h1423 | h1423
                                          · rcases p1410_3 (m.d 0 3) (by simp) with h1424 | h1424
                                            · linarith only [h1424, h966, hlam]
                                            · rcases p1410_3 (m.d 0 4) (by simp) with h1426 | h1426
                                              · linarith only [h1426, h967, hlam]
                                              · rcases p1410_3 (m.d 0 5) (by simp) with h1428 | h1428
                                                · linarith only [h1428, h968, hlam]
                                                · linarith only [h1326, h1428, hlam]
                                          · linarith only [h1423, h970, hlam]
                                        · linarith only [h1422, h967, hlam]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        rcases p1410_3 (m.d 0 1) (by simp) with h1433 | h1433
                                        · rcases p1410_3 (m.d 0 2) (by simp) with h1434 | h1434
                                          · rcases p1410_3 (m.d 0 3) (by simp) with h1435 | h1435
                                            · linarith only [h1435, h966, hlam]
                                            · rcases p1410_3 (m.d 0 4) (by simp) with h1437 | h1437
                                              · linarith only [h1437, h967, hlam]
                                              · rcases p1410_3 (m.d 0 5) (by simp) with h1439 | h1439
                                                · linarith only [h1439, h968, hlam]
                                                · rcases h2bigk with h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c | h1441c
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [hlam, p1441_0]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [h0, hlam, p1441_1]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    rcases p1441_3 (m.d 0 2) (by simp) with h1444 | h1444
                                                    · rcases p1441_3 (m.d 1 2) (by simp) with h1445 | h1445
                                                      · rcases p1441_3 (m.d 2 3) (by simp) with h1446 | h1446
                                                        · linarith only [h1446, hlam, p1441_0]
                                                        · rcases p1441_3 (m.d 2 4) (by simp) with h1448 | h1448
                                                          · linarith only [h1448, h970, hlam]
                                                          · linarith only [h1402, h1448, hlam]
                                                      · linarith only [h1393, h1445, hlam]
                                                    · linarith only [h1444, hlam, p1441_0]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    rcases p1441_3 (m.d 0 2) (by simp) with h1453 | h1453
                                                    · rcases p1441_3 (m.d 1 2) (by simp) with h1454 | h1454
                                                      · rcases p1441_3 (m.d 2 3) (by simp) with h1455 | h1455
                                                        · linarith only [h1455, h969, hlam]
                                                        · rcases p1441_3 (m.d 2 4) (by simp) with h1457 | h1457
                                                          · linarith only [h1457, hlam, p1441_0]
                                                          · rcases p1441_3 (m.d 2 5) (by simp) with h1459 | h1459
                                                            · linarith only [h1459, h971, hlam]
                                                            · linarith only [h1406, h1459, hlam]
                                                      · linarith only [h1394, h1454, hlam]
                                                    · linarith only [h1453, hlam, p1441_0]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    rcases p1441_3 (m.d 0 2) (by simp) with h1464 | h1464
                                                    · rcases p1441_3 (m.d 1 2) (by simp) with h1465 | h1465
                                                      · rcases p1441_3 (m.d 2 3) (by simp) with h1466 | h1466
                                                        · linarith only [h1466, h969, hlam]
                                                        · rcases p1441_3 (m.d 2 4) (by simp) with h1468 | h1468
                                                          · linarith only [h1468, h970, hlam]
                                                          · rcases p1441_3 (m.d 2 5) (by simp) with h1470 | h1470
                                                            · linarith only [h1470, hlam, p1441_0]
                                                            · rcases h2emin with h1472 | h1472 | h1472 | h1472 | h1472
                                                              · rcases h5bigk with h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c | h1473c
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [hlam, p1473_0]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [h0, h1395, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1410_1, p1473_1]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [h0, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1410_1, p1473_1]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [h1263, hlam, p1473_1]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [h1326, hlam, p1473_1]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [h968, hlam, p1473_0]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [hlam, p1473_0]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [h0, h968, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p1473_1]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [h1398, hlam, p1473_1]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [h1400, hlam, p1473_1]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [h971, hlam, p1473_1]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [h1395, hlam, p1473_1]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [hlam, p1473_0]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [h1404, hlam, p1473_1]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [h1406, hlam, p1473_1]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [h1263, h1393, h966, hc23, hlam, hphi, p1473_1, u3elo4]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [h1393, h1398, hc23, hlam, hphi, p1473_1, u3elo4]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [h1404, hc23, hlam, hphi, p1473_1, u3elo4]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [hlam, p1473_0]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [h1408, hlam, p1473_1]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  rcases p1473_3 (m.d 0 5) (by simp) with h1494 | h1494
                                                                  · linarith only [h1326, h1494, hlam]
                                                                  · rcases p1473_3 (m.d 1 5) (by simp) with h1496 | h1496
                                                                    · linarith only [h1400, h1496, hlam]
                                                                    · rcases p1473_3 (m.d 2 5) (by simp) with h1498 | h1498
                                                                      · linarith only [h1406, h1498, hlam]
                                                                      · rcases p1473_3 (m.d 3 5) (by simp) with h1500 | h1500
                                                                        · linarith only [h1408, h1500, hlam]
                                                                        · linarith only [h1263, h1500, hlam]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  rcases p1473_3 (m.d 0 5) (by simp) with h1503 | h1503
                                                                  · linarith only [h1326, h1503, hlam]
                                                                  · linarith only [h1503, h968, hlam]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  rcases p1473_3 (m.d 0 5) (by simp) with h1506 | h1506
                                                                  · linarith only [h1326, h1506, hlam]
                                                                  · linarith only [h1506, h971, hlam]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [h1263, h1393, h966, hc23, hc45, hlam, hphi, ht34, p1473_1]
                                                                · have p1473_0 := h1473c.1
                                                                  have p1473_1 := h1473c.2.1
                                                                  have p1473_2 := h1473c.2.2.1
                                                                  have p1473_3 := h1473c.2.2.2
                                                                  linarith only [hlam, p1473_0]
                                                              · rcases h5bigk with h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c | h1511c
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [hlam, p1511_0]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [h0, h1400, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1410_1, p1511_1]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [h0, h1402, h1406, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1410_1, p1511_1]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [h1263, hlam, p1511_1]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [h1326, hlam, p1511_1]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [h968, hlam, p1511_0]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [hlam, p1511_0]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [h0, h1402, h1406, h968, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1511_1]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [h1398, hlam, p1511_1]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [h1400, hlam, p1511_1]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [h971, hlam, p1511_1]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [h1395, hlam, p1511_1]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [hlam, p1511_0]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [h1404, hlam, p1511_1]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [h1406, hlam, p1511_1]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [h1402, h1406, h971, hc23, hlam, hphi, p1511_1, u3elo4]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [h1395, h1402, h1406, hc23, hlam, hphi, p1511_1, u3elo4]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [h1402, h1406, hc23, hlam, hphi, p1511_1, u3elo4]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [hlam, p1511_0]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [h1408, hlam, p1511_1]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  rcases p1511_3 (m.d 0 5) (by simp) with h1532 | h1532
                                                                  · linarith only [h1326, h1532, hlam]
                                                                  · rcases p1511_3 (m.d 1 5) (by simp) with h1534 | h1534
                                                                    · linarith only [h1400, h1534, hlam]
                                                                    · rcases p1511_3 (m.d 2 5) (by simp) with h1536 | h1536
                                                                      · linarith only [h1406, h1536, hlam]
                                                                      · rcases p1511_3 (m.d 3 5) (by simp) with h1538 | h1538
                                                                        · linarith only [h1408, h1538, hlam]
                                                                        · linarith only [h1263, h1538, hlam]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  rcases p1511_3 (m.d 0 5) (by simp) with h1541 | h1541
                                                                  · linarith only [h1326, h1541, hlam]
                                                                  · linarith only [h1541, h968, hlam]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  rcases p1511_3 (m.d 0 5) (by simp) with h1544 | h1544
                                                                  · linarith only [h1326, h1544, hlam]
                                                                  · linarith only [h1544, h971, hlam]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [h1263, h1393, h966, hc23, hc45, hlam, hphi, ht34, p1511_1]
                                                                · have p1511_0 := h1511c.1
                                                                  have p1511_1 := h1511c.2.1
                                                                  have p1511_2 := h1511c.2.2.1
                                                                  have p1511_3 := h1511c.2.2.2
                                                                  linarith only [hlam, p1511_0]
                                                              · linarith only [h1393, h1472, h966, h972, hlam, ht23, u3elo3]
                                                              · linarith only [h0, h1394, h1472, h967, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                                              · linarith only [h0, h1395, h1472, h968, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                                                      · linarith only [h1395, h1465, hlam]
                                                    · linarith only [h1464, hlam, p1441_0]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [h0, h1326, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1410_1, p1441_1]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [hlam, p1441_0]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [h0, h1326, h1393, h966, h972, hlam, p1410_1, p1441_2]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [h0, h1326, h1394, h967, hlam, p1410_1, p1441_2]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [h0, h1395, h968, hlam, p1410_1, p1441_2]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [h969, hlam, p1441_0]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [h1393, hlam, p1441_0]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [hlam, p1441_0]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [h1402, hlam, p1441_0]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [h1404, hlam, p1441_0]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [h970, hlam, p1441_0]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [h1394, hlam, p1441_0]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [h1326, h1394, h967, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1410_1, p1441_1, u0elo0]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [hlam, p1441_0]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [h1406, hlam, p1441_1]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [h971, hlam, p1441_0]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [h1395, hlam, p1441_0]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [h0, h1395, h968, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1410_1, p1441_1, u0elo1]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [h0, h1395, h968, hc24, hlam, hphi, ht0b, ht45, ht5b, p1410_1, p1441_1, u0elo1]
                                                  · have p1441_0 := h1441c.1
                                                    have p1441_1 := h1441c.2.1
                                                    have p1441_2 := h1441c.2.2.1
                                                    have p1441_3 := h1441c.2.2.2
                                                    linarith only [hlam, p1441_0]
                                          · linarith only [h1434, h971, hlam]
                                        · linarith only [h1433, h968, hlam]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        linarith only [h1393, h966, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1410_1, u0elo1]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        linarith only [hlam, p1410_0]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        rcases p1410_3 (m.d 0 1) (by simp) with h1578 | h1578
                                        · linarith only [h0, h1578, hlam]
                                        · linarith only [h1578, h966, hlam]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        rcases p1410_3 (m.d 0 1) (by simp) with h1581 | h1581
                                        · linarith only [h0, h1581, hlam]
                                        · linarith only [h1581, h967, hlam]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        rcases p1410_3 (m.d 0 1) (by simp) with h1584 | h1584
                                        · linarith only [h0, h1584, hlam]
                                        · linarith only [h1584, h968, hlam]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        linarith only [h966, hlam, p1410_1]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        linarith only [h969, hlam, p1410_1]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        linarith only [hlam, p1410_0]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        linarith only [h972, hlam, p1410_1]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        linarith only [h1263, hlam, p1410_1]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        linarith only [h967, hlam, p1410_0]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        linarith only [h970, hlam, p1410_0]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        linarith only [h1393, h1408, h966, h972, hc23, hc45, hlam, hphi, ht34, p1410_1]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        linarith only [hlam, p1410_0]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        linarith only [h1326, hlam, p1410_0]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        linarith only [h968, hlam, p1410_0]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        linarith only [h971, hlam, p1410_1]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        linarith only [h1263, h1393, h966, hc23, hlam, hphi, p1410_1, u3elo4]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        linarith only [h1263, h1393, h1396, h967, hc23, hlam, hphi, p1410_1, u3elo4]
                                      · have p1410_0 := h1410c.1
                                        have p1410_1 := h1410c.2.1
                                        have p1410_2 := h1410c.2.2.1
                                        have p1410_3 := h1410c.2.2.2
                                        linarith only [hlam, p1410_0]
                      · linarith only [h0, h1395, h971, hlam]
                    · linarith only [h0, h1394, h970, hlam]
                  · linarith only [h0, h1393, h968, hc15, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo2]
          · linarith only [h0, h968, h971, hlam]
        · linarith only [h0, h967, h970, hlam]
      · linarith only [h0, h966, h969, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1608 | h1608
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1609 | h1609
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1610 | h1610
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1611 | h1611
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1612 | h1612
              · linarith only [h1612, h966, h968, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1614 | h1614
                · linarith only [h1611, h1614, h966, h968, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1616 | h1616
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1617 | h1617
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1618 | h1618
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1619 | h1619
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1620 | h1620
                          · linarith only [h1612, h1620, h966, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h1619, h1620, h966, h968, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
                        · linarith only [h1611, h1612, h1616, h1619, h966, h968, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h1610, h1618, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1609, h1617, hlam]
                  · linarith only [h0, h1616, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1627 | h1627
              · linarith only [h1611, h1627, h967, h968, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1629 | h1629
                · linarith only [h1629, h967, h968, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1631 | h1631
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1632 | h1632
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1633 | h1633
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1634 | h1634
                        · linarith only [h1611, h1634, h966, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1636 | h1636
                          · linarith only [h1627, h1636, h966, h968, hlam]
                          · linarith only [h1631, h1634, h1636, h967, h968, hc23, hlam, hphi, u3elo4]
                      · linarith only [h0, h1610, h1633, h967, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                    · linarith only [h0, h1609, h1632, hlam]
                  · linarith only [h0, h1631, hc01, hlam, hphi, ht12, ht23, u3elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1642 | h1642
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1643 | h1643
              · linarith only [h0, h1610, h1643, h966, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1645 | h1645
                · linarith only [h0, h1610, h1645, h967, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1647 | h1647
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1648 | h1648
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1649 | h1649
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1650 | h1650
                        · linarith only [h0, h1610, h1649, h1650, h966, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h1642, h1643, h1650, hc13, hlam, hphi, u3elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1653 | h1653
                        · linarith only [h0, h1649, h1653, h966, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h1642, h1643, h1647, h1653, hc23, hlam, hphi, u3elo4]
                    · linarith only [h0, h1609, h1610, h1643, h1647, h1648, h966, hc23, hlam, hphi, u3elo4]
                  · linarith only [h0, h1647, hc01, hlam, hphi, ht12, ht23, u3elo2]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1658 | h1658
              · linarith only [h1642, h1658, h966, h968, hc13, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1660 | h1660
                · linarith only [h0, h1610, h1660, h967, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1662 | h1662
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1663 | h1663
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1664 | h1664
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1665 | h1665
                        · linarith only [h0, h1610, h1664, h1665, h966, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1667 | h1667
                          · linarith only [h0, h1610, h1658, h1664, h1665, h1667, h967, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · linarith only [h1662, h1665, h1667, h967, h968, hc23, hlam, hphi, u3elo4]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1670 | h1670
                        · linarith only [h1642, h1670, h966, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 5 (by decide) (by decide) with h1672 | h1672
                          · linarith only [h0, h1610, h1658, h1672, h966, hlam]
                          · linarith only [h0, h1662, h1664, h1670, h1672, h967, hc23, hlam, hphi, u3elo4]
                    · linarith only [h0, h1609, h1663, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1662, h966, hc13, hlam, hphi, u3elo2]
        · linarith only [h0, h1609, h967, hlam]
      · linarith only [h0, h1608, h966, hc13, hlam, hphi, u3elo2]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1679 | h1679
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1680 | h1680
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1681 | h1681
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1682 | h1682
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1683 | h1683
            · linarith only [h1683, h966, h967, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1685 | h1685
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1686 | h1686
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1687 | h1687
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1688 | h1688
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1689 | h1689
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1690 | h1690
                        · linarith only [h1683, h1690, h966, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h1690, h966, h967, hc13, hlam, hphi, u3elo3]
                      · linarith only [h1682, h1687, h1688, h1689, h966, h967, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1681, h1687, h1688, h966, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1687, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1685, h1686, h966, h967, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1697 | h1697
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1698 | h1698
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1699 | h1699
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1700 | h1700
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1701 | h1701
                        · linarith only [h1683, h1701, h966, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h1701, h966, h967, hc13, hlam, hphi, u3elo3]
                      · linarith only [h1682, h1698, h1699, h1700, h966, h967, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1681, h1699, hlam]
                  · linarith only [h0, h1698, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h1679, h1697, h967, hlam]
          · linarith only [h1679, h1681, h1682, h967, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1709 | h1709
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1710 | h1710
            · linarith only [h0, h1681, h1710, h966, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1712 | h1712
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1713 | h1713
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1714 | h1714
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1715 | h1715
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1716 | h1716
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1717 | h1717
                        · linarith only [h1710, h1717, h966, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h0, h1681, h1714, h1715, h1717, h966, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h1681, h1714, h1715, h1716, h966, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1721 | h1721
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1722 | h1722
                        · linarith only [h0, h1681, h1710, h1715, h1722, h966, hc02, hc24, hlam, hphi]
                        · linarith only [h0, h1714, h1715, h1722, h966, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h1709, h1714, h1721, h966, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1714, hc01, hlam, hphi, ht12, ht23, u3elo2]
                · linarith only [h0, h1681, h1712, h1713, h966, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1728 | h1728
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1729 | h1729
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1730 | h1730
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1731 | h1731
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1732 | h1732
                        · linarith only [h0, h1710, h1732, h966, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h0, h1681, h1729, h1730, h1732, h966, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h1681, h1729, h1730, h1731, h966, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1736 | h1736
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1737 | h1737
                        · linarith only [h0, h1710, h1730, h1737, h966, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1729, h1730, h1737, h966, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h1709, h1729, h1736, h966, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1729, h966, hc13, hlam, hphi, u3elo2]
                · linarith only [h0, h1679, h1681, h1728, hlam]
          · linarith only [h0, h1679, h1709, hlam]
      · linarith only [h0, h1680, h966, hc13, hlam, hphi, u3elo2]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1745 | h1745
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1746 | h1746
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1747 | h1747
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1748 | h1748
            · linarith only [h1748, h966, h967, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1750 | h1750
              · linarith only [h1679, h1750, h966, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1752 | h1752
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1753 | h1753
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1754 | h1754
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1755 | h1755
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1756 | h1756
                        · linarith only [h1748, h1756, h966, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h1753, h1756, h966, h967, hc23, hlam, hphi, u3elo3]
                      · linarith only [h1747, h1753, h1754, h1755, h966, h967, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1746, h1753, h1754, h966, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h1753, h966, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1762 | h1762
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1763 | h1763
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1764 | h1764
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1765 | h1765
                        · linarith only [h1752, h1765, h966, h967, hc34, hc45, hlam, hphi]
                        · linarith only [h1765, h966, h967, hc13, hlam, hphi, u3elo3]
                      · linarith only [h1747, h1762, h1763, h1764, h966, h967, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1746, h1752, h1762, h1763, h966, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h1762, h966, hc13, hlam, hphi, u3elo2]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1771 | h1771
            · linarith only [h1771, h966, h967, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1773 | h1773
              · linarith only [h0, h1747, h1773, h966, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1775 | h1775
                · linarith only [h1746, h1747, h1775, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1777 | h1777
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1778 | h1778
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1779 | h1779
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1780 | h1780
                        · linarith only [h1771, h1780, h966, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h1777, h1780, h966, h967, hc23, hlam, hphi, u3elo3]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1783 | h1783
                        · linarith only [h1775, h1783, h966, h967, hc34, hc45, hlam, hphi]
                        · linarith only [h1783, h966, h967, hc13, hlam, hphi, u3elo3]
                    · linarith only [h0, h1746, h1777, h1778, h966, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1777, h966, hc13, hlam, hphi, u3elo2]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1788 | h1788
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1789 | h1789
            · linarith only [h0, h1746, h1789, h966, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1791 | h1791
              · linarith only [h1679, h1789, h1791, h966, hc13, hlam, hphi, u3elo3]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1793 | h1793
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1794 | h1794
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1795 | h1795
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1796 | h1796
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1797 | h1797
                        · linarith only [h1679, h1746, h1788, h1789, h1795, h1797, h966, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h1746, h1794, h1795, h1797, h966, hc23, hlam, hphi, u3elo3]
                      · linarith only [h1679, h1746, h1788, h1794, h1795, h1796, h966, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1801 | h1801
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1802 | h1802
                        · linarith only [h0, h1795, h1802, h966, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h1679, h1795, h1801, h1802, h966, hc13, hlam, hphi, u3elo3]
                      · linarith only [h0, h1788, h1794, h1801, h966, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h0, h1794, h966, hc13, hlam, hphi, u3elo2]
                · linarith only [h1746, h1788, h1793, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1808 | h1808
            · linarith only [h0, h1746, h1808, h966, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1810 | h1810
              · linarith only [h1679, h1810, h966, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1812 | h1812
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1813 | h1813
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1814 | h1814
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1815 | h1815
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1816 | h1816
                        · linarith only [h1808, h1816, h966, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                        · linarith only [h0, h1746, h1813, h1814, h1816, h966, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h1746, h1813, h1814, h1815, h966, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1820 | h1820
                      · linarith only [h0, h1788, h1813, h1814, h1820, h966, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1822 | h1822
                        · linarith only [h1808, h1812, h1822, h966, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h0, h1814, h1822, h966, hc13, hlam, hphi, u3elo3]
                  · linarith only [h0, h1813, h966, hc13, hlam, hphi, u3elo2]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h1826 | h1826
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h1827 | h1827
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1828 | h1828
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1829 | h1829
                        · linarith only [h0, h1746, h1827, h1829, h966, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h0, h1746, h1826, h1827, h1829, h966, hc23, hlam, hphi, u3elo3]
                      · linarith only [h0, h1746, h1826, h1827, h1828, h966, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h1833 | h1833
                      · linarith only [h0, h1788, h1826, h1827, h1833, h966, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h1835 | h1835
                        · linarith only [h0, h1827, h1835, h966, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · linarith only [h0, h1826, h1827, h1835, h966, hc23, hlam, hphi, u3elo3]
                  · linarith only [h0, h1826, hc01, hlam, hphi, ht12, ht23, u3elo2]
      · linarith only [h0, h1745, h966, hc13, hlam, hphi, u3elo2]

end R2N4
