import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5862000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h903 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h904 | h904
  · rcases m.htr 0 1 5 (by decide) (by decide) with h905 | h905
    · rcases m.htr 0 2 3 (by decide) (by decide) with h906 | h906
      · rcases m.htr 0 3 4 (by decide) (by decide) with h907 | h907
        · rcases m.htr 0 3 5 (by decide) (by decide) with h908 | h908
          · rcases m.htr 1 2 3 (by decide) (by decide) with h909 | h909
            · rcases m.htr 1 2 4 (by decide) (by decide) with h910 | h910
              · rcases m.htr 1 2 5 (by decide) (by decide) with h911 | h911
                · rcases m.htr 1 3 4 (by decide) (by decide) with h912 | h912
                  · linarith only [h903, h912, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h914 | h914
                    · linarith only [h907, h912, h914, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h916 | h916
                      · linarith only [h0, h904, h916, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h918 | h918
                        · linarith only [h906, h912, h918, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h920 | h920
                          · linarith only [h0, h903, h909, h914, h916, h920, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h922 | h922
                            · linarith only [h910, h916, h922, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h924 | h924
                              · linarith only [h0, h903, h907, h910, h916, h924, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
                              · rcases h1bigk with h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c | h926c
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h0, hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  rcases p926_3 (m.d 0 1) (by simp) with h929 | h929
                                  · rcases p926_3 (m.d 1 2) (by simp) with h930 | h930
                                    · rcases p926_3 (m.d 1 3) (by simp) with h931 | h931
                                      · linarith only [h931, hlam, p926_0]
                                      · rcases p926_3 (m.d 1 4) (by simp) with h933 | h933
                                        · linarith only [h904, h933, hlam]
                                        · linarith only [h912, h933, hlam]
                                    · linarith only [h909, h930, hlam]
                                  · linarith only [h929, hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h0, h910, hlam, hphi, ht0b, ht45, ht5b, p926_1, u0elo1, u4ehi2]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h0, h910, h916, hlam, hphi, ht0b, ht45, ht5b, p926_1, u0elo1, u4ehi2]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h903, h908, h912, h924, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p926_1]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h0, h903, h908, h912, h924, hlam, p926_2]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  rcases p926_3 (m.d 0 1) (by simp) with h943 | h943
                                  · linarith only [h0, h943, hlam]
                                  · linarith only [h904, h943, hlam]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  rcases p926_3 (m.d 0 1) (by simp) with h946 | h946
                                  · linarith only [h0, h946, hlam]
                                  · linarith only [h905, h946, hlam]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h903, hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h909, hlam, p926_1]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h912, hlam, p926_1]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h914, hlam, p926_1]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h904, hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h910, hlam, p926_1]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h904, h909, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p926_1, u0elo0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h916, hlam, p926_1]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h905, hlam, p926_0]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h911, hlam, p926_1]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h908, h909, h914, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p926_1, u0elo2]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [h0, h903, h908, h914, hlam, hphi, ht0b, ht45, ht5b, p926_1, u0elo1, u4ehi1]
                                · have p926_0 := h926c.1
                                  have p926_1 := h926c.2.1
                                  have p926_2 := h926c.2.2.1
                                  have p926_3 := h926c.2.2.2
                                  linarith only [hlam, p926_0]
                · linarith only [h0, h904, h910, h911, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · linarith only [h0, h903, h907, h910, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · linarith only [h0, h903, h907, h909, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h967 | h967
            · rcases m.htr 1 2 4 (by decide) (by decide) with h968 | h968
              · rcases m.htr 1 2 5 (by decide) (by decide) with h969 | h969
                · rcases m.htr 1 3 4 (by decide) (by decide) with h970 | h970
                  · linarith only [h903, h970, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · linarith only [h907, h908, h967, h970, hc23, hc35, hlam, hphi]
                · linarith only [h0, h903, h907, h969, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · linarith only [h0, h905, h907, h908, h968, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · linarith only [h0, h905, h907, h908, h967, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h976 | h976
          · rcases m.htr 1 2 3 (by decide) (by decide) with h977 | h977
            · rcases m.htr 1 2 4 (by decide) (by decide) with h978 | h978
              · rcases m.htr 1 2 5 (by decide) (by decide) with h979 | h979
                · rcases m.htr 1 3 4 (by decide) (by decide) with h980 | h980
                  · linarith only [h903, h907, h980, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h982 | h982
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h983 | h983
                      · linarith only [h0, h904, h983, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                      · linarith only [h980, h982, h983, hlam]
                    · linarith only [h907, h976, h977, h982, hc23, hc34, hlam, hphi]
                · linarith only [h0, h904, h978, h979, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · linarith only [h0, h904, h978, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h904, h977, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h990 | h990
            · rcases m.htr 1 2 4 (by decide) (by decide) with h991 | h991
              · rcases m.htr 1 2 5 (by decide) (by decide) with h992 | h992
                · rcases m.htr 1 3 4 (by decide) (by decide) with h993 | h993
                  · linarith only [h0, h903, h907, h993, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h995 | h995
                    · linarith only [h903, h976, h995, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h997 | h997
                      · linarith only [h0, h904, h997, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h999 | h999
                        · linarith only [h903, h907, h990, h999, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1001 | h1001
                          · linarith only [h0, h1001, h903, h905, h976, h990, h991, h997, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1003 | h1003
                            · linarith only [h1003, h991, h997, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1005 | h1005
                              · rcases h1bigk with h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c | h1006c
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [hlam, p1006_0]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [h0, hlam, p1006_0]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  rcases p1006_3 (m.d 0 1) (by simp) with h1009 | h1009
                                  · rcases p1006_3 (m.d 1 2) (by simp) with h1010 | h1010
                                    · rcases p1006_3 (m.d 1 3) (by simp) with h1011 | h1011
                                      · linarith only [h1011, hlam, p1006_0]
                                      · rcases p1006_3 (m.d 1 4) (by simp) with h1013 | h1013
                                        · linarith only [h1013, h904, hlam]
                                        · linarith only [h1013, h993, hlam]
                                    · linarith only [h1010, h990, hlam]
                                  · linarith only [h1009, hlam, p1006_0]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [h0, h991, hlam, hphi, ht0b, ht45, ht5b, p1006_1, u0elo1, u4ehi2]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [h0, h991, h997, hlam, hphi, ht0b, ht45, ht5b, p1006_1, u0elo1, u4ehi2]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [h904, h991, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1006_1, u4ehi2]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [hlam, p1006_0]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  rcases p1006_3 (m.d 0 1) (by simp) with h1022 | h1022
                                  · linarith only [h0, h1022, hlam]
                                  · linarith only [h1022, h903, hlam]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  rcases p1006_3 (m.d 0 1) (by simp) with h1025 | h1025
                                  · linarith only [h0, h1025, hlam]
                                  · linarith only [h1025, h904, hlam]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  rcases p1006_3 (m.d 0 1) (by simp) with h1028 | h1028
                                  · linarith only [h0, h1028, hlam]
                                  · linarith only [h1028, h905, hlam]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [h903, hlam, p1006_0]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [h990, hlam, p1006_1]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [hlam, p1006_0]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [h993, hlam, p1006_1]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [h995, hlam, p1006_1]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [h904, hlam, p1006_0]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [h991, hlam, p1006_1]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [h905, h997, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1006_1, u0elo0]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [hlam, p1006_0]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [h997, hlam, p1006_1]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [h905, hlam, p1006_0]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [h992, hlam, p1006_1]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [h0, h905, h990, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1006_1]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [h0, h905, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1006_1, u4ehi1]
                                · have p1006_0 := h1006c.1
                                  have p1006_1 := h1006c.2.1
                                  have p1006_2 := h1006c.2.2.1
                                  have p1006_3 := h1006c.2.2.2
                                  linarith only [hlam, p1006_0]
                              · rcases h1bigk with h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c | h1046c
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [hlam, p1046_0]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [h0, hlam, p1046_0]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  rcases p1046_3 (m.d 0 1) (by simp) with h1049 | h1049
                                  · rcases p1046_3 (m.d 1 2) (by simp) with h1050 | h1050
                                    · rcases p1046_3 (m.d 1 3) (by simp) with h1051 | h1051
                                      · linarith only [h1051, hlam, p1046_0]
                                      · rcases p1046_3 (m.d 1 4) (by simp) with h1053 | h1053
                                        · linarith only [h1053, h904, hlam]
                                        · linarith only [h1053, h993, hlam]
                                    · linarith only [h1050, h990, hlam]
                                  · linarith only [h1049, hlam, p1046_0]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [h0, h991, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1046_1, u4ehi2]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [h0, h991, h997, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1046_1, u4ehi2]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [h904, h991, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1046_1, u4ehi2]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [hlam, p1046_0]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  rcases p1046_3 (m.d 0 1) (by simp) with h1062 | h1062
                                  · linarith only [h0, h1062, hlam]
                                  · linarith only [h1062, h903, hlam]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  rcases p1046_3 (m.d 0 1) (by simp) with h1065 | h1065
                                  · linarith only [h0, h1065, hlam]
                                  · linarith only [h1065, h904, hlam]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  rcases p1046_3 (m.d 0 1) (by simp) with h1068 | h1068
                                  · linarith only [h0, h1068, hlam]
                                  · linarith only [h1068, h905, hlam]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [h903, hlam, p1046_0]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [h990, hlam, p1046_1]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [hlam, p1046_0]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [h993, hlam, p1046_1]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [h995, hlam, p1046_1]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [h904, hlam, p1046_0]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [h991, hlam, p1046_1]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [h905, h997, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1046_1, u0elo0]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [hlam, p1046_0]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [h997, hlam, p1046_1]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [h905, hlam, p1046_0]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [h992, hlam, p1046_1]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [h0, h905, h990, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1046_1]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [h0, h905, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1046_1, u4ehi1]
                                · have p1046_0 := h1046c.1
                                  have p1046_1 := h1046c.2.1
                                  have p1046_2 := h1046c.2.2.1
                                  have p1046_3 := h1046c.2.2.2
                                  linarith only [hlam, p1046_0]
                · linarith only [h0, h904, h991, h992, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · linarith only [h0, h904, h991, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h904, h990, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
      · linarith only [h0, h903, h906, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1090 | h1090
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1091 | h1091
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1092 | h1092
          · linarith only [h1092, h903, h905, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1094 | h1094
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1095 | h1095
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1096 | h1096
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1097 | h1097
                  · linarith only [h1097, h903, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · linarith only [h1091, h1092, h1094, h1097, hc23, hc35, hlam, hphi]
                · linarith only [h0, h1091, h1096, h903, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
              · linarith only [h0, h1091, h1095, h903, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · linarith only [h0, h1091, h1094, h903, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1103 | h1103
          · linarith only [h1091, h1103, h904, h905, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1105 | h1105
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1106 | h1106
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1107 | h1107
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1108 | h1108
                  · linarith only [h1091, h1108, h903, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1110 | h1110
                    · linarith only [h1103, h1110, h903, h904, h905, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi1]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1112 | h1112
                      · linarith only [h1112, h904, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                      · linarith only [h1112, h904, h905, hc45, hlam, hphi, u4ehi1]
                · linarith only [h0, h1106, h1107, h904, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
              · linarith only [h0, h1106, h904, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h1105, h904, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
      · linarith only [h0, h1090, h903, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1119 | h1119
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1120 | h1120
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1121 | h1121
        · linarith only [h1121, h903, h904, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1123 | h1123
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1124 | h1124
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1125 | h1125
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1126 | h1126
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1127 | h1127
                  · linarith only [h0, h1121, h1127, h903, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1129 | h1129
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1130 | h1130
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1131 | h1131
                        · linarith only [h1124, h1127, h1131, h903, h904, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1133 | h1133
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1134 | h1134
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1135 | h1135
                              · linarith only [h1129, h1135, h903, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                              · linarith only [h1119, h1126, h1127, h1134, h1135, h903, h904, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                            · linarith only [h1129, h1130, h1134, h903, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                          · linarith only [h1123, h1127, h1133, h903, h904, hc23, hc34, hlam, hphi]
                      · linarith only [h1130, h903, h904, hc13, hc45, hlam, hphi, ht34]
                    · linarith only [h1123, h1124, h1127, h1129, h903, h904, hc23, hc34, hlam, hphi]
                · linarith only [h1119, h1125, h1126, h904, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1143 | h1143
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1144 | h1144
                  · linarith only [h1121, h1123, h1144, h903, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1146 | h1146
                    · linarith only [h0, h1125, h1146, h903, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · linarith only [h0, h1123, h1124, h1125, h1146, h903, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · linarith only [h0, h1119, h1143, hlam]
            · linarith only [h0, h1120, h1124, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1151 | h1151
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1152 | h1152
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1153 | h1153
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1154 | h1154
                  · linarith only [h1154, h903, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1156 | h1156
                    · linarith only [h1123, h1156, h903, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1158 | h1158
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1159 | h1159
                        · linarith only [h1119, h1151, h1154, h1156, h1159, h904, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1161 | h1161
                          · linarith only [h1123, h1151, h1161, h903, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1163 | h1163
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1164 | h1164
                              · rcases h1bigk with h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c | h1165c
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h0, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1154, h904, hc13, hc34, hlam, hphi, p1165_1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h904, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1153, h1154, h1163, h904, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1165_1, u4ehi4]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1119, h1153, h1163, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1165_1, u4ehi4]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  rcases p1165_3 (m.d 0 1) (by simp) with h1173 | h1173
                                  · linarith only [h0, h1173, hlam]
                                  · linarith only [h1173, h903, hlam]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1119, h1153, h1163, h904, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1165_1, u4ehi4]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  rcases p1165_3 (m.d 0 1) (by simp) with h1177 | h1177
                                  · linarith only [h0, h1177, hlam]
                                  · linarith only [h1119, h1177, hlam]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h903, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1151, hlam, p1165_1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1154, hlam, p1165_1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1156, hlam, p1165_1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1119, h1153, h1163, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1165_1, u4ehi4]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1152, hlam, p1165_1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  rcases p1165_3 (m.d 0 1) (by simp) with h1187 | h1187
                                  · linarith only [h1187, h904, hlam]
                                  · linarith only [h1187, h903, hlam]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  rcases p1165_3 (m.d 0 1) (by simp) with h1191 | h1191
                                  · linarith only [h1191, h904, hlam]
                                  · linarith only [h1119, h1191, hlam]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1119, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1153, hlam, p1165_1]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1119, h1151, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1165_1, u0elo0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [h1158, hlam, p1165_0]
                                · have p1165_0 := h1165c.1
                                  have p1165_1 := h1165c.2.1
                                  have p1165_2 := h1165c.2.2.1
                                  have p1165_3 := h1165c.2.2.2
                                  linarith only [hlam, p1165_0]
                              · linarith only [h1119, h1153, h1154, h1163, h1164, h904, hlam]
                            · linarith only [h1119, h1154, h1158, h1163, h904, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                      · linarith only [h1151, h1158, h903, h904, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h1119, h1152, h1153, h904, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1203 | h1203
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1204 | h1204
                  · linarith only [h1204, h903, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1206 | h1206
                    · linarith only [h1123, h1206, h903, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1208 | h1208
                      · linarith only [h0, h1119, h1152, h1208, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h1119, h1151, h1206, h1208, h904, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h1119, h1203, hlam]
            · linarith only [h0, h1120, h1151, hlam]
      · linarith only [h0, h1120, h903, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1214 | h1214
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1215 | h1215
        · linarith only [h1215, h903, h904, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h1217 | h1217
          · linarith only [h1119, h1217, h903, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1219 | h1219
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1220 | h1220
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1221 | h1221
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1222 | h1222
                  · linarith only [h0, h1215, h1222, h903, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1224 | h1224
                    · linarith only [h1119, h1217, h1224, h903, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1226 | h1226
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1227 | h1227
                        · linarith only [h1119, h1214, h1222, h1226, h1227, h903, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1229 | h1229
                          · linarith only [h1119, h1219, h1224, h1229, h903, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1231 | h1231
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1232 | h1232
                              · rcases h1bigk with h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c | h1233c
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [hlam, p1233_0]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [h0, hlam, p1233_0]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [h1119, h1219, h1222, h1226, hc23, hc34, hlam, hphi, p1233_1]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [h904, hlam, p1233_0]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [h1119, hlam, p1233_0]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  rcases p1233_3 (m.d 0 1) (by simp) with h1239 | h1239
                                  · linarith only [h1239, hlam, p1233_0]
                                  · rcases p1233_3 (m.d 1 2) (by simp) with h1241 | h1241
                                    · rcases p1233_3 (m.d 1 3) (by simp) with h1242 | h1242
                                      · linarith only [h1219, h1242, hlam]
                                      · rcases p1233_3 (m.d 1 4) (by simp) with h1244 | h1244
                                        · linarith only [h1220, h1244, hlam]
                                        · linarith only [h1244, h904, hlam]
                                    · linarith only [h1241, hlam, p1233_0]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [hlam, p1233_0]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  rcases p1233_3 (m.d 0 1) (by simp) with h1249 | h1249
                                  · linarith only [h0, h1249, hlam]
                                  · linarith only [h1249, h903, hlam]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [h904, hc01, hc12, hlam, hphi, p1233_1]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [h1119, h1219, h903, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1233_1]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [h903, hlam, p1233_0]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [h1219, hlam, p1233_1]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [hlam, p1233_0]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [h1222, hlam, p1233_1]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [h1224, hlam, p1233_1]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [h1219, h1222, h903, hc23, hc34, hlam, hphi, p1233_1]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [h1220, hlam, p1233_1]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  rcases p1233_3 (m.d 0 1) (by simp) with h1261 | h1261
                                  · linarith only [h1261, h904, hlam]
                                  · linarith only [h1261, h903, hlam]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [hlam, p1233_0]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [h1119, h1219, h1222, h903, hc23, hc34, hlam, hphi, p1233_1]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [h1219, h1224, h903, hc23, hc35, hlam, hphi, p1233_1]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [h1221, hlam, p1233_1]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  rcases p1233_3 (m.d 0 1) (by simp) with h1268 | h1268
                                  · linarith only [h1119, h1268, hlam]
                                  · linarith only [h1268, h903, hlam]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [h1226, hlam, p1233_0]
                                · have p1233_0 := h1233c.1
                                  have p1233_1 := h1233c.2.1
                                  have p1233_2 := h1233c.2.2.1
                                  have p1233_3 := h1233c.2.2.2
                                  linarith only [hlam, p1233_0]
                              · linarith only [h1219, h1222, h1231, h1232, h903, h904, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1274 | h1274
                              · rcases h1bigk with h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c | h1275c
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [hlam, p1275_0]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [h0, hlam, p1275_0]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [h1219, h1222, h904, hc23, hc34, hlam, hphi, p1275_1]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [h904, hlam, p1275_0]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [h1119, hlam, p1275_0]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  rcases p1275_3 (m.d 0 1) (by simp) with h1281 | h1281
                                  · linarith only [h1281, hlam, p1275_0]
                                  · rcases p1275_3 (m.d 1 2) (by simp) with h1283 | h1283
                                    · rcases p1275_3 (m.d 1 3) (by simp) with h1284 | h1284
                                      · linarith only [h1219, h1284, hlam]
                                      · rcases p1275_3 (m.d 1 4) (by simp) with h1286 | h1286
                                        · linarith only [h1220, h1286, hlam]
                                        · linarith only [h1286, h904, hlam]
                                    · linarith only [h1283, hlam, p1275_0]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [hlam, p1275_0]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  rcases p1275_3 (m.d 0 1) (by simp) with h1291 | h1291
                                  · linarith only [h0, h1291, hlam]
                                  · linarith only [h1291, h903, hlam]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [h1226, h1231, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1275_1, u4ehi2]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [h1119, hc01, hc12, hlam, hphi, p1275_1]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [h903, hlam, p1275_0]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [h1219, hlam, p1275_1]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [hlam, p1275_0]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [h1222, hlam, p1275_1]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [h1224, hlam, p1275_1]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [h1222, h903, hc13, hc34, hlam, hphi, p1275_1]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [h1220, hlam, p1275_1]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  rcases p1275_3 (m.d 0 1) (by simp) with h1303 | h1303
                                  · linarith only [h1303, h904, hlam]
                                  · linarith only [h1303, h903, hlam]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [hlam, p1275_0]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [h1119, h1219, h1222, h903, hc23, hc34, hlam, hphi, p1275_1]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [h1219, h1224, h903, hc23, hc35, hlam, hphi, p1275_1]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [h1221, hlam, p1275_1]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  rcases p1275_3 (m.d 0 1) (by simp) with h1310 | h1310
                                  · linarith only [h1119, h1310, hlam]
                                  · linarith only [h1310, h903, hlam]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [h1226, hlam, p1275_0]
                                · have p1275_0 := h1275c.1
                                  have p1275_1 := h1275c.2.1
                                  have p1275_2 := h1275c.2.2.1
                                  have p1275_3 := h1275c.2.2.2
                                  linarith only [hlam, p1275_0]
                              · linarith only [h1222, h1226, h1274, hlam]
                      · linarith only [h1219, h1226, h903, h904, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1317 | h1317
                  · linarith only [h1317, h903, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1319 | h1319
                    · linarith only [h1220, h1221, h1319, h903, h904, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1321 | h1321
                      · linarith only [h1220, h1221, h1321, hlam]
                      · linarith only [h1219, h1321, h903, h904, hc23, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1324 | h1324
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1325 | h1325
                  · linarith only [h1325, h903, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1327 | h1327
                    · linarith only [h0, h1220, h1327, h903, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1329 | h1329
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1330 | h1330
                        · linarith only [h1219, h1325, h1330, h903, h904, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi0]
                        · linarith only [h1119, h1220, h1324, h1330, h903, hc13, hc34, hlam, hphi]
                      · linarith only [h1119, h1219, h1220, h1324, h1329, h903, hc23, hc45, hlam, hphi, ht34]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1334 | h1334
                  · linarith only [h1334, h903, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1336 | h1336
                    · linarith only [h0, h1324, h1336, h903, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1338 | h1338
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1339 | h1339
                        · linarith only [h0, h1219, h1324, h1334, h1338, h1339, h903, hlam]
                        · linarith only [h0, h1220, h1339, h903, hc13, hc34, hlam, hphi]
                      · linarith only [h1219, h1338, h903, h904, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h0, h1214, h1219, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
      · linarith only [h0, h1214, h903, hlam]

set_option maxHeartbeats 5862000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h903 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1345 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1346 | h1346
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1347 | h1347
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1348 | h1348
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1349 | h1349
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1350 | h1350
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1351 | h1351
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1352 | h1352
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1353 | h1353
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1354 | h1354
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1355 | h1355
                    · linarith only [h1345, h1355, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1357 | h1357
                      · linarith only [h1347, h1357, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1359 | h1359
                        · linarith only [h1347, h1348, h1357, h1359, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1361 | h1361
                          · linarith only [h1351, h1355, h1361, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1363 | h1363
                            · linarith only [h1353, h1355, h1363, hlam]
                            · rcases h1bigk with h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c | h1365c
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [hlam, p1365_0]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [h0, hlam, p1365_0]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [h903, hlam, p1365_0]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [h1353, h1357, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1365_1, u0elo0]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [h1347, h1353, h1355, h1357, h903, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1365_1, u0elo1]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [h1345, h1353, h1357, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1365_1]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [hlam, p1365_0]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [h1346, h1353, h1355, h1357, h903, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1365_1]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                rcases p1365_3 (m.d 0 1) (by simp) with h1374 | h1374
                                · linarith only [h0, h1374, hlam]
                                · linarith only [h1345, h1374, hlam]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                rcases p1365_3 (m.d 0 1) (by simp) with h1377 | h1377
                                · linarith only [h0, h1377, hlam]
                                · linarith only [h1346, h1377, hlam]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [h1346, h1353, h1355, h1357, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1365_1]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [h1350, hlam, p1365_1]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [hlam, p1365_0]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                rcases p1365_3 (m.d 0 1) (by simp) with h1383 | h1383
                                · linarith only [h1383, h903, hlam]
                                · linarith only [h1345, h1383, hlam]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                rcases p1365_3 (m.d 0 1) (by simp) with h1386 | h1386
                                · linarith only [h1386, h903, hlam]
                                · linarith only [h1346, h1386, hlam]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [h1345, hlam, p1365_0]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [h1351, hlam, p1365_1]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [h1353, hlam, p1365_0]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [hlam, p1365_0]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [h1355, hlam, p1365_1]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [h1346, hlam, p1365_0]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [h1352, hlam, p1365_1]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [h1354, hlam, p1365_0]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [h1346, h1353, h1357, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1365_1, u0elo0]
                              · have p1365_0 := h1365c.1
                                have p1365_1 := h1365c.2.1
                                have p1365_2 := h1365c.2.2.1
                                have p1365_3 := h1365c.2.2.2
                                linarith only [hlam, p1365_0]
                  · linarith only [h1345, h1353, h1354, h903, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                · linarith only [h1345, h1351, h1353, h903, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
              · linarith only [h0, h1345, h1351, h1352, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · linarith only [h1345, h1350, h1351, h903, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · linarith only [h0, h1345, h1350, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
        · linarith only [h1346, h1349, h903, hlam]
      · linarith only [h1345, h1348, h903, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1406 | h1406
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1407 | h1407
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1408 | h1408
          · linarith only [h0, h1345, h1347, h1408, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
          · linarith only [h0, h1345, h1408, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
        · linarith only [h0, h1346, h1347, h1407, hlam]
      · linarith only [h0, h1345, h1347, h1406, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1413 | h1413
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1414 | h1414
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1415 | h1415
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1416 | h1416
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1417 | h1417
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1418 | h1418
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1419 | h1419
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1420 | h1420
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1421 | h1421
                    · linarith only [h1345, h1421, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                    · linarith only [h1345, h1346, h1421, hc45, hlam, hphi, u4ehi1]
                  · linarith only [h1345, h1413, h1415, h1419, h1420, h903, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                · linarith only [h1345, h1419, h903, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
              · linarith only [h1345, h1416, h1417, h1418, h903, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · linarith only [h1345, h1416, h1417, h903, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · linarith only [h0, h1345, h1413, h1416, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1429 | h1429
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1430 | h1430
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1431 | h1431
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1432 | h1432
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1433 | h1433
                  · linarith only [h1345, h1415, h1429, h1430, h1433, h903, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                  · linarith only [h1345, h1430, h1433, h903, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                · linarith only [h1345, h1430, h1432, h903, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
              · linarith only [h0, h1345, h1430, h1431, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
            · linarith only [h1345, h1429, h1430, h903, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
          · linarith only [h0, h1345, h1413, h1429, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
      · linarith only [h1345, h1414, h903, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1441 | h1441
      · rcases m.htr 0 3 5 (by decide) (by decide) with h1442 | h1442
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1443 | h1443
          · linarith only [h0, h1345, h1413, h1443, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
          · linarith only [h0, h1345, h1443, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1446 | h1446
          · linarith only [h0, h1345, h1413, h1446, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
          · linarith only [h0, h1345, h1446, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
      · linarith only [h0, h1345, h1413, h1441, hlam]

set_option maxHeartbeats 5862000 in
theorem r1l7_20_11_13_14_M_LI_L_I_L_I_L_R_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h903 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1345 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1450 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1451 | h1451
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1452 | h1452
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1453 | h1453
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1454 | h1454
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1455 | h1455
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1456 | h1456
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1457 | h1457
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1458 | h1458
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1459 | h1459
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1460 | h1460
                    · linarith only [h1451, h1460, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1462 | h1462
                      · linarith only [h1452, h1460, h1462, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1464 | h1464
                        · linarith only [h1451, h1452, h1460, h1464, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                        · linarith only [h1450, h1459, h1464, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                  · linarith only [h1345, h1450, h1459, hlam]
                · linarith only [h1453, h1458, h903, hlam]
              · linarith only [h1451, h1452, h1457, h903, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
            · linarith only [h0, h1450, h1451, h1452, h1456, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1471 | h1471
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1472 | h1472
              · linarith only [h1454, h1455, h1472, hlam]
              · linarith only [h0, h1451, h1452, h1455, h1472, h903, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h0, h1450, h1451, h1452, h1471, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
        · linarith only [h0, h1451, h1454, hlam]
      · linarith only [h1450, h1453, h903, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1478 | h1478
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1479 | h1479
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1480 | h1480
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1481 | h1481
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1482 | h1482
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1483 | h1483
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1484 | h1484
                  · linarith only [h1450, h1452, h1479, h1482, h1484, h903, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h1450, h1452, h1482, h1484, h903, hlam]
                · linarith only [h1452, h1482, h1483, h903, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1488 | h1488
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1489 | h1489
                  · linarith only [h1450, h1482, h1489, h903, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · linarith only [h1450, h1482, h1489, h903, hlam]
                · linarith only [h1478, h1488, h903, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h1450, h1479, h1481, h903, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1494 | h1494
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1495 | h1495
              · linarith only [h1450, h1452, h1479, h1480, h1495, h903, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1497 | h1497
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1498 | h1498
                  · linarith only [h0, h1450, h1480, h1498, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h1450, h1479, h1480, h1498, h903, hlam]
                · linarith only [h1478, h1497, h903, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h1450, h1479, h1494, h903, hlam]
        · linarith only [h0, h1451, h1479, hlam]
      · linarith only [h1450, h1478, h903, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1505 | h1505
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1506 | h1506
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1507 | h1507
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1508 | h1508
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1509 | h1509
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1510 | h1510
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1511 | h1511
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1512 | h1512
                  · linarith only [h0, h1450, h1451, h1507, h1512, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h1345, h1450, h1512, hlam]
                · linarith only [h1506, h1511, h903, hlam]
              · linarith only [h1451, h1505, h1507, h1510, hlam]
            · linarith only [h0, h1451, h1507, h1509, hc01, hc25, hlam, hphi, ht12]
          · linarith only [h1451, h1505, h1507, h1508, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1519 | h1519
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1520 | h1520
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1521 | h1521
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1522 | h1522
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1523 | h1523
                  · linarith only [h1345, h1450, h1507, h1519, h1523, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h1345, h1450, h1523, hlam]
                · linarith only [h1506, h1522, h903, hlam]
              · linarith only [h0, h1450, h1505, h1507, h1521, hc15, hlam, hphi, ht0b, ht5b, u0elo2]
            · linarith only [h0, h1450, h1520, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1529 | h1529
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1530 | h1530
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1531 | h1531
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1532 | h1532
                  · linarith only [h0, h1450, h1507, h1532, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h1450, h1519, h1532, hlam]
                · linarith only [h1506, h1531, h903, hlam]
              · linarith only [h1505, h1530, h903, hlam]
            · linarith only [h0, h1450, h1529, hlam]
      · linarith only [h0, h1450, h1451, h1506, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1539 | h1539
      · rcases m.htr 1 2 3 (by decide) (by decide) with h1540 | h1540
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1541 | h1541
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1542 | h1542
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1543 | h1543
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1544 | h1544
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1545 | h1545
                  · linarith only [h0, h1450, h1451, h1505, h1540, h1543, h1545, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h1450, h1451, h1505, h1543, h1545, hlam]
                · linarith only [h0, h1451, h1505, h1543, h1544, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1549 | h1549
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1550 | h1550
                  · linarith only [h0, h1450, h1451, h1540, h1543, h1550, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h1450, h1451, h1540, h1543, h1550, hlam]
                · linarith only [h1451, h1539, h1540, h1549, hlam]
            · linarith only [h0, h1450, h1451, h1540, h1542, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · linarith only [h0, h1450, h1451, h1540, h1541, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h1556 | h1556
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1557 | h1557
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1558 | h1558
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1559 | h1559
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1560 | h1560
                  · linarith only [h0, h1450, h1540, h1560, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h1450, h1451, h1505, h1558, h1560, hlam]
                · linarith only [h1505, h1539, h1540, h1556, h1558, h1559, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · linarith only [h1540, h1556, h1558, hlam]
            · linarith only [h0, h1450, h1557, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h1566 | h1566
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1567 | h1567
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1568 | h1568
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1569 | h1569
                  · linarith only [h0, h1450, h1540, h1569, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h1450, h1451, h1505, h1567, h1569, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                · linarith only [h0, h1451, h1505, h1567, h1568, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1573 | h1573
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1574 | h1574
                  · linarith only [h0, h1450, h1540, h1567, h1574, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · linarith only [h0, h1450, h1540, h1567, h1574, hlam]
                · linarith only [h0, h1539, h1540, h1573, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
            · linarith only [h0, h1450, h1566, hlam]
      · linarith only [h0, h1450, h1451, h1539, hlam]

end R2N4
