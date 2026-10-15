import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_51S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_13_24_L_R_H_I_x0_x1 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h941 | h941
  · rcases m.htr 0 1 5 (by decide) (by decide) with h942 | h942
    · rcases m.htr 0 2 3 (by decide) (by decide) with h943 | h943
      · linarith only [h0, h1, h943, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h945 | h945
        · rcases m.htr 0 3 4 (by decide) (by decide) with h946 | h946
          · rcases m.htr 0 4 5 (by decide) (by decide) with h947 | h947
            · rcases m.htr 1 2 3 (by decide) (by decide) with h948 | h948
              · linarith only [h0, h943, h945, h948, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h950 | h950
                · rcases m.htr 1 3 4 (by decide) (by decide) with h951 | h951
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h952 | h952
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h953 | h953
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h954 | h954
                        · linarith only [h0, h1, h948, h950, h954, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h1, h948, h954, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h1, h945, h947, h948, h951, h953, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h1, h952, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h0, h1, h946, h950, h951, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h1, h945, h948, h950, hc12, hc23, hlam, hphi]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h961 | h961
              · linarith only [h0, h1, h961, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h963 | h963
                · rcases m.htr 1 3 4 (by decide) (by decide) with h964 | h964
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h965 | h965
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h966 | h966
                      · linarith only [h1, h941, h947, h961, h966, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h968 | h968
                        · linarith only [h0, h1, h961, h963, h968, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h1, h941, h961, h963, h964, h968, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h0, h1, h963, h964, h965, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h0, h1, h963, h964, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h0, h1, h945, h961, h963, hc12, hc23, hlam, hphi]
          · linarith only [h0, h1, h945, h946, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h975 | h975
          · rcases m.htr 0 4 5 (by decide) (by decide) with h976 | h976
            · rcases m.htr 1 2 3 (by decide) (by decide) with h977 | h977
              · linarith only [h0, h1, h977, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h979 | h979
                · linarith only [h0, h1, h945, h977, h979, hc02, hc23, hlam, hphi]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h981 | h981
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h982 | h982
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h983 | h983
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h984 | h984
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h985 | h985
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h986 | h986
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h987 | h987
                              · rcases h4bigk with h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c | h988c
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h1, h941, h977, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p988_1]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h945, hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h1, h941, h977, h987, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p988_1, u3ehi4]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h1, h941, h977, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p988_1]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h941, hlam, p988_1]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h979, hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h987, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p988_1, u3ehi4]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h1, h941, h977, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p988_1]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h0, h945, hc12, hc24, hlam, hphi, p988_1]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h979, hc12, hc24, hlam, hphi, p988_1]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h984, h987, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p988_1, u3ehi4]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  rcases p988_3 (m.d 0 4) (by simp) with h1003 | h1003
                                  · linarith only [h1003, h945, hlam]
                                  · linarith only [h1003, h976, hlam]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h975, hlam, p988_1]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h981, hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h984, hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h1, h941, h977, h981, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p988_1]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h976, hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h983, hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h986, hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [h987, hlam, p988_0]
                                · have p988_0 := h988c.1
                                  have p988_1 := h988c.2.1
                                  have p988_2 := h988c.2.2.1
                                  have p988_3 := h988c.2.2.2
                                  linarith only [hlam, p988_0]
                              · linarith only [h1, h941, h976, h977, h987, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h1, h941, h977, h983, h986, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h1, h941, h977, h983, h985, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                        · linarith only [h1, h941, h977, h981, h984, hlam]
                      · linarith only [h1, h941, h976, h977, h981, h983, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h1, h982, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h941, h975, h981, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1023 | h1023
              · linarith only [h0, h1, h1023, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1025 | h1025
                · linarith only [h0, h1025, h945, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1027 | h1027
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1028 | h1028
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1029 | h1029
                      · linarith only [h1, h1023, h1029, h941, h976, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1031 | h1031
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1032 | h1032
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1033 | h1033
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1034 | h1034
                              · linarith only [h1027, h1034, h941, h976, hlam]
                              · rcases h4bigk with h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c | h1036c
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h1025, h1033, h976, hc12, hc24, hlam, hphi, p1036_1]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h945, hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h1033, h976, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1036_1, u3ehi3]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h976, hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h941, hlam, p1036_1]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h1025, hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h1029, h942, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1036_1, u3ehi3]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h1029, hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h0, h945, hc12, hc24, hlam, hphi, p1036_1]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h1025, hc12, hc24, hlam, hphi, p1036_1]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h1031, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1036_1, u3ehi3]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h1027, h1031, h941, h976, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1036_1, u3ehi3]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h975, hlam, p1036_1]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h1027, hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h1031, hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h1034, hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h1027, h941, hc45, hlam, hphi, ht34, p1036_1, u3ehi3]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h1027, hc45, hlam, hphi, ht34, p1036_1, u3ehi3]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h1033, hlam, p1036_0]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [h1031, h1033, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1036_1, u3ehi3]
                                · have p1036_0 := h1036c.1
                                  have p1036_1 := h1036c.2.1
                                  have p1036_2 := h1036c.2.2.1
                                  have p1036_3 := h1036c.2.2.2
                                  linarith only [hlam, p1036_0]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1062 | h1062
                              · linarith only [h1, h1023, h1027, h1033, h1062, h941, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                              · rcases h4bigk with h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c | h1064c
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [hlam, p1064_0]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [h1027, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1064_1, u3ehi3]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [h945, hlam, p1064_0]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1064_1, u3ehi3]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [h976, hlam, p1064_0]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [h941, hlam, p1064_1]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [hlam, p1064_0]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [h1025, hlam, p1064_0]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [h1, h1023, h1029, h942, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1064_1, u3ehi3]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [h1029, hlam, p1064_0]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [h1033, hc04, hc45, hlam, hphi, p1064_1]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [h1033, hc14, hc45, hlam, hphi, p1064_1]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [hlam, p1064_0]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [h1033, hc45, hlam, hphi, ht34, p1064_1, u3ehi3]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [h1033, hlam, p1064_0]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [h975, hlam, p1064_1]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [h1027, hlam, p1064_0]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [h1031, hlam, p1064_0]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [hlam, p1064_0]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [h1062, hlam, p1064_0]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [h1027, h941, hc45, hlam, hphi, ht34, p1064_1, u3ehi3]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [h1027, hc45, hlam, hphi, ht34, p1064_1, u3ehi3]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [hc24, hc45, hlam, hphi, p1064_1]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [hc45, hlam, hphi, ht34, p1064_1, u3ehi3]
                                · have p1064_0 := h1064c.1
                                  have p1064_1 := h1064c.2.1
                                  have p1064_2 := h1064c.2.2.1
                                  have p1064_3 := h1064c.2.2.2
                                  linarith only [hlam, p1064_0]
                          · linarith only [h1, h1023, h1028, h1032, h942, hlam]
                        · linarith only [h1, h1023, h1027, h1029, h1031, h942, hlam]
                    · linarith only [h0, h1, h1028, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h1027, h942, h975, h976, hlam]
          · linarith only [h1, h941, h975, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1095 | h1095
      · linarith only [h0, h1, h1095, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1097 | h1097
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1098 | h1098
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1099 | h1099
            · linarith only [h0, h1097, h1099, h942, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1101 | h1101
              · linarith only [h0, h1, h1095, h1101, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1103 | h1103
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1104 | h1104
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1105 | h1105
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1106 | h1106
                      · linarith only [h0, h1097, h1099, h1106, h941, h942, hlam]
                      · linarith only [h0, h1103, h1106, h942, hc24, hc45, hlam, hphi]
                    · linarith only [h0, h1, h1103, h1104, h1105, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h0, h1, h1104, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h0, h1, h1097, h1101, h1103, hc12, hc23, hlam, hphi]
          · linarith only [h1, h1098, h941, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1113 | h1113
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1114 | h1114
            · linarith only [h1114, h941, h942, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1116 | h1116
              · linarith only [h0, h1, h1095, h1116, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1118 | h1118
                · linarith only [h0, h1097, h1118, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1120 | h1120
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1121 | h1121
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1122 | h1122
                      · linarith only [h1097, h1114, h1116, h1121, h1122, h941, h942, hc02, hc23, hlam, hphi]
                      · linarith only [h1120, h1122, h941, h942, hc45, hlam, hphi, ht34, u3ehi3]
                    · linarith only [h1, h1120, h1121, h941, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h0, h1, h1120, hc12, hc34, hlam, hphi, ht23]
          · linarith only [h1, h1113, h941, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1128 | h1128
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1129 | h1129
      · linarith only [h0, h1, h1129, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1131 | h1131
        · linarith only [h0, h1131, h941, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1133 | h1133
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1134 | h1134
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1135 | h1135
              · linarith only [h0, h1, h1129, h1135, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1137 | h1137
                · linarith only [h0, h1131, h1137, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1139 | h1139
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1140 | h1140
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1141 | h1141
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1142 | h1142
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1143 | h1143
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1144 | h1144
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1145 | h1145
                              · rcases h4bigk with h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c | h1146c
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [hlam, p1146_0]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [h941, hlam, p1146_0]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [h1131, hlam, p1146_0]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [h1133, h1145, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, p1146_1, u3ehi4]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  rcases p1146_3 (m.d 0 4) (by simp) with h1151 | h1151
                                  · rcases p1146_3 (m.d 1 4) (by simp) with h1152 | h1152
                                    · rcases p1146_3 (m.d 2 4) (by simp) with h1153 | h1153
                                      · rcases p1146_3 (m.d 3 4) (by simp) with h1154 | h1154
                                        · linarith only [h1133, h1154, hlam]
                                        · linarith only [h1145, h1154, hlam]
                                      · linarith only [h1144, h1153, hlam]
                                    · linarith only [h1141, h1152, hlam]
                                  · linarith only [h1151, hlam, p1146_0]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [h1135, h1139, h941, hc01, hc23, hlam, hphi, ht12, p1146_1]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [hlam, p1146_0]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [h1137, hlam, p1146_0]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [h1135, h1139, h1145, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1146_1, u3ehi4]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  rcases p1146_3 (m.d 0 4) (by simp) with h1164 | h1164
                                  · linarith only [h1164, h941, hlam]
                                  · linarith only [h1134, h1164, hlam]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [h1128, h1140, h1142, h941, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1146_1, u3ehi4]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [h1128, h1140, h1142, h941, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1146_1, u3ehi4]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [hlam, p1146_0]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [h1142, h1145, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1146_1, u3ehi4]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  rcases p1146_3 (m.d 0 4) (by simp) with h1171 | h1171
                                  · linarith only [h1131, h1171, hlam]
                                  · linarith only [h1134, h1171, hlam]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [h1133, hlam, p1146_1]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [h1139, hlam, p1146_0]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [h1142, hlam, p1146_0]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [hlam, p1146_0]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [h1, h1133, h1135, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1146_1]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [h1134, hlam, p1146_0]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [h1141, hlam, p1146_0]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [h1144, hlam, p1146_0]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [h1145, hlam, p1146_0]
                                · have p1146_0 := h1146c.1
                                  have p1146_1 := h1146c.2.1
                                  have p1146_2 := h1146c.2.2.1
                                  have p1146_3 := h1146c.2.2.2
                                  linarith only [hlam, p1146_0]
                              · linarith only [h1128, h1137, h1141, h1142, h1145, h941, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h1128, h1137, h1141, h1144, h941, hlam]
                          · linarith only [h0, h1137, h1142, h1143, h941, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1128, h1135, h1139, h1140, h1142, h941, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h1128, h1140, h1141, h941, hc45, hlam, hphi, ht34, u3ehi4]
                    · linarith only [h0, h1139, h1140, h941, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h1, h1133, h1139, hlam]
            · linarith only [h1128, h1134, h941, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1192 | h1192
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1193 | h1193
              · linarith only [h0, h1193, h941, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1195 | h1195
                · linarith only [h0, h1131, h1195, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1197 | h1197
                  · linarith only [h0, h1, h1133, h1193, h1197, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h1197, hc12, hc34, hlam, hphi, ht23]
            · linarith only [h1, h1128, h1133, h1192, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1201 | h1201
      · linarith only [h0, h1, h1201, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1203 | h1203
        · linarith only [h0, h1203, h941, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1205 | h1205
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1206 | h1206
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1207 | h1207
              · linarith only [h0, h1, h1201, h1207, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1209 | h1209
                · linarith only [h0, h1128, h1203, h1206, h1209, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1211 | h1211
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1212 | h1212
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1213 | h1213
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1214 | h1214
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1215 | h1215
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1216 | h1216
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1217 | h1217
                              · rcases h4bigk with h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c | h1218c
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [hlam, p1218_0]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [h941, hlam, p1218_0]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [h1203, hlam, p1218_0]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [h1205, h1217, hc03, hc45, hlam, hphi, ht0b, ht5b, p1218_1]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  rcases p1218_3 (m.d 0 4) (by simp) with h1223 | h1223
                                  · rcases p1218_3 (m.d 1 4) (by simp) with h1224 | h1224
                                    · rcases p1218_3 (m.d 2 4) (by simp) with h1225 | h1225
                                      · rcases p1218_3 (m.d 3 4) (by simp) with h1226 | h1226
                                        · linarith only [h1205, h1226, hlam]
                                        · linarith only [h1217, h1226, hlam]
                                      · linarith only [h1216, h1225, hlam]
                                    · linarith only [h1213, h1224, hlam]
                                  · linarith only [h1223, hlam, p1218_0]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [h1207, h1211, h941, hc01, hc23, hlam, hphi, ht12, p1218_1]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [hlam, p1218_0]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [h1209, hlam, p1218_0]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [h1207, h1211, h1217, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1218_1, u3ehi4]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  rcases p1218_3 (m.d 0 4) (by simp) with h1236 | h1236
                                  · linarith only [h1236, h941, hlam]
                                  · linarith only [h1206, h1236, hlam]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [h0, h1128, h1206, hc12, hc24, hlam, hphi, p1218_1]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [h0, h941, hc12, hc24, hlam, hphi, p1218_1]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [hlam, p1218_0]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [h1214, h1217, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1218_1, u3ehi4]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  rcases p1218_3 (m.d 0 4) (by simp) with h1243 | h1243
                                  · linarith only [h1203, h1243, hlam]
                                  · linarith only [h1206, h1243, hlam]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [h1205, hlam, p1218_1]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [h1211, hlam, p1218_0]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [h1214, hlam, p1218_0]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [hlam, p1218_0]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [h1, h1205, h1207, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1218_1]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [h1206, hlam, p1218_0]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [h1213, hlam, p1218_0]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [h1216, hlam, p1218_0]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [h1217, hlam, p1218_0]
                                · have p1218_0 := h1218c.1
                                  have p1218_1 := h1218c.2.1
                                  have p1218_2 := h1218c.2.2.1
                                  have p1218_3 := h1218c.2.2.2
                                  linarith only [hlam, p1218_0]
                              · rcases h4bigk with h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c | h1256c
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [hlam, p1256_0]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h941, hlam, p1256_0]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h1203, hlam, p1256_0]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h1, h1205, h1207, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1256_1, u3ehi3]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h1, h1205, h1207, h1217, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1256_1, u3ehi3]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h0, h1207, h1211, h941, hc12, hc23, hlam, hphi, p1256_1]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [hlam, p1256_0]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h1209, hlam, p1256_0]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h1207, h1211, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1256_1, u3ehi3]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h1207, h1211, h1217, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1256_1, u3ehi3]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h1206, h1214, h1217, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1256_1, u3ehi3]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h0, h1214, h941, hc12, hc23, hlam, hphi, p1256_1]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [hlam, p1256_0]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h1214, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1256_1, u3ehi3]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h1214, h1217, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1256_1, u3ehi3]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h1205, hlam, p1256_1]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h1211, hlam, p1256_0]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h1214, hlam, p1256_0]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [hlam, p1256_0]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h1217, hlam, p1256_0]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h1206, hlam, p1256_0]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h1213, hlam, p1256_0]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h1216, hlam, p1256_0]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [h1206, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1256_1, u3ehi3]
                                · have p1256_0 := h1256c.1
                                  have p1256_1 := h1256c.2.1
                                  have p1256_2 := h1256c.2.2.1
                                  have p1256_3 := h1256c.2.2.2
                                  linarith only [hlam, p1256_0]
                            · linarith only [h0, h1, h1205, h1206, h1207, h1209, h1216, h941, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h1207, h1215, hc12, hc35, hlam, hphi, ht23]
                        · linarith only [h1207, h1212, h1214, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h0, h1205, h1206, h1213, h941, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · linarith only [h1, h1205, h1212, hc35, hlam, hphi, u3ehi3]
                  · linarith only [h1, h1205, h1211, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1288 | h1288
              · linarith only [h0, h1288, h941, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1290 | h1290
                · linarith only [h0, h1206, h1290, h941, hc24, hc45, hlam, hphi]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1292 | h1292
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1293 | h1293
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1294 | h1294
                      · linarith only [h0, h1206, h1288, h1292, h1294, h941, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h1294, h941, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h0, h1, h1293, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h0, h1, h1205, h1292, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1299 | h1299
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1300 | h1300
              · linarith only [h0, h1300, h941, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1302 | h1302
                · linarith only [h0, h1203, h1302, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1304 | h1304
                  · linarith only [h0, h1, h1205, h1300, h1304, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h1304, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1307 | h1307
              · linarith only [h0, h1, h1307, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1309 | h1309
                · linarith only [h0, h1, h1205, h1299, h1309, hc24, hc45, hlam, hphi]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1311 | h1311
                  · linarith only [h0, h1, h1205, h1307, h1311, hc12, hc23, hlam, hphi]
                  · linarith only [h0, h1, h1311, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_13_24_L_R_H_I_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_13_24_L_R_H_I_x0_x0 m hb3 hb4 h0 h1
  · exact r1l7_13_24_L_R_H_I_x0_x1 m hb3 hb4 h0 h1

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_13_24_L_R_H_I_x1_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1314 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1315 | h1315
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1316 | h1316
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1317 | h1317
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1318 | h1318
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1319 | h1319
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1320 | h1320
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1321 | h1321
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1322 | h1322
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1323 | h1323
                  · linarith only [h0, h1314, h1323, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h1314, h1319, h1321, h1323, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h1314, h1319, h1322, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h0, h1314, h1321, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1328 | h1328
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1329 | h1329
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1330 | h1330
                  · linarith only [h0, h1314, h1330, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h1314, h1319, h1330, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h0, h1314, h1319, h1329, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h0, h1314, h1319, h1328, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1335 | h1335
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1336 | h1336
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1337 | h1337
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1338 | h1338
                  · linarith only [h1314, h1319, h1338, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1340 | h1340
                    · linarith only [h1314, h1319, h1340, hc34, hlam, hphi, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1342 | h1342
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1343 | h1343
                        · linarith only [h1317, h1319, h1343, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1345 | h1345
                          · linarith only [h1336, h1340, h1345, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1347 | h1347
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1348 | h1348
                              · rcases h4bigk with h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c | h1349c
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [hlam, p1349_0]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [h1337, h1347, hc04, hc45, hlam, hphi, ht0b, ht5b, p1349_1]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [h0, h1315, h1347, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1349_1]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [h1319, hlam, p1349_0]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [h0, h1315, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1349_1]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [h1315, hlam, p1349_1]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [hlam, p1349_0]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [h1347, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p1349_1]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [h1338, hlam, p1349_1]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [h0, h1315, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1349_1]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [h1318, hlam, p1349_1]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [h1337, hlam, p1349_1]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [hlam, p1349_0]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [h1343, hlam, p1349_1]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [h0, h1318, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1349_1]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [h1314, h1319, h1336, hc34, hlam, hphi, p1349_1, u3ehi2]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [h1336, h1338, hc34, hlam, hphi, p1349_1, u3ehi2]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [h1343, hc34, hlam, hphi, p1349_1, u3ehi2]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [hlam, p1349_0]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  rcases p1349_3 (m.d 0 4) (by simp) with h1369 | h1369
                                  · linarith only [h1319, h1369, hlam]
                                  · linarith only [h1335, h1369, hlam]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [h1335, hlam, p1349_0]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [h1342, hlam, p1349_0]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [h1347, hlam, p1349_0]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [h1348, hlam, p1349_0]
                                · have p1349_0 := h1349c.1
                                  have p1349_1 := h1349c.2.1
                                  have p1349_2 := h1349c.2.2.1
                                  have p1349_3 := h1349c.2.2.2
                                  linarith only [hlam, p1349_0]
                              · linarith only [h1314, h1319, h1336, h1348, hc45, hlam, hphi, ht34, u3ehi2]
                            · linarith only [h0, h1315, h1342, h1347, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h1315, h1335, h1336, h1338, h1342, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h1314, h1336, h1337, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1314, h1336, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1382 | h1382
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1383 | h1383
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1384 | h1384
                  · linarith only [h0, h1314, h1384, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1386 | h1386
                    · linarith only [h0, h1314, h1386, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h1388 | h1388
                      · linarith only [h0, h1315, h1319, h1335, h1388, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h1390 | h1390
                        · linarith only [h1314, h1319, h1382, h1390, hlam]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h1392 | h1392
                          · linarith only [h1382, h1386, h1392, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h1394 | h1394
                            · linarith only [h1315, h1335, h1383, h1394, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h1396 | h1396
                              · linarith only [h1314, h1319, h1335, h1382, h1396, hc34, hlam, hphi, u3ehi2]
                              · linarith only [h1314, h1319, h1382, h1396, hc45, hlam, hphi, ht34, u3ehi2]
                · linarith only [h0, h1314, h1382, h1383, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1314, h1382, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
        · linarith only [h0, h1315, h1318, hlam]
      · linarith only [h0, h1314, h1317, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1403 | h1403
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1404 | h1404
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1405 | h1405
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1406 | h1406
            · linarith only [h1314, h1316, h1405, h1406, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1408 | h1408
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1409 | h1409
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1410 | h1410
                  · linarith only [h0, h1314, h1410, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h0, h1314, h1405, h1410, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi1]
                · linarith only [h0, h1314, h1405, h1409, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
              · linarith only [h0, h1314, h1405, h1408, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1415 | h1415
            · linarith only [h1315, h1316, h1415, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1417 | h1417
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1418 | h1418
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1419 | h1419
                  · linarith only [h1314, h1405, h1419, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1421 | h1421
                    · linarith only [h0, h1315, h1419, h1421, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                    · linarith only [h1315, h1316, h1417, h1419, h1421, hc35, hlam, hphi, u3ehi2]
                · linarith only [h0, h1314, h1417, h1418, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1314, h1417, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
        · linarith only [h0, h1315, h1404, hlam]
      · linarith only [h0, h1314, h1403, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1428 | h1428
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1429 | h1429
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1430 | h1430
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1431 | h1431
          · linarith only [h1314, h1315, h1431, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1433 | h1433
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1434 | h1434
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1435 | h1435
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1436 | h1436
                  · linarith only [h1314, h1431, h1436, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h1314, h1315, h1434, h1436, hc34, hlam, hphi, u3ehi2]
                · linarith only [h0, h1430, h1435, hlam]
              · linarith only [h0, h1314, h1434, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h1314, h1315, h1433, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1442 | h1442
          · linarith only [h0, h1314, h1430, h1442, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1444 | h1444
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1445 | h1445
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1446 | h1446
                · linarith only [h0, h1314, h1430, h1445, h1446, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h1314, h1445, h1446, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1314, h1445, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h1314, h1315, h1444, hc45, hlam, hphi, ht34, u3ehi1]
      · linarith only [h0, h1314, h1429, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1452 | h1452
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1453 | h1453
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1454 | h1454
          · linarith only [h1314, h1315, h1454, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1456 | h1456
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1457 | h1457
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1458 | h1458
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1459 | h1459
                  · linarith only [h1314, h1454, h1459, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                  · linarith only [h1314, h1315, h1457, h1459, hc34, hlam, hphi, u3ehi2]
                · linarith only [h0, h1314, h1453, h1457, h1458, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1314, h1457, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h1314, h1315, h1456, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h1465 | h1465
          · linarith only [h0, h1314, h1453, h1465, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h1467 | h1467
            · rcases m.htr 1 2 3 (by decide) (by decide) with h1468 | h1468
              · rcases m.htr 1 2 4 (by decide) (by decide) with h1469 | h1469
                · linarith only [h0, h1314, h1453, h1468, h1469, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h1314, h1468, h1469, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
              · linarith only [h0, h1314, h1468, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · linarith only [h0, h1314, h1453, h1467, hc45, hlam, hphi, ht34, u3ehi1]
      · linarith only [h0, h1314, h1452, hlam]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_13_24_L_R_H_I_x1_x1_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1314 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1475 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1476 | h1476
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1477 | h1477
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1478 | h1478
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1479 | h1479
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1480 | h1480
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1481 | h1481
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1482 | h1482
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1483 | h1483
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1484 | h1484
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1485 | h1485
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1486 | h1486
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1487 | h1487
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1488 | h1488
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1489 | h1489
                            · rcases h4bigk with h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c | h1490c
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [hlam, p1490_0]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1475, h1482, h1487, h1488, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p1490_1, u3ehi4]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1314, h1475, h1481, h1487, h1488, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1490_1, u3ehi4]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1314, h1475, h1481, h1489, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1490_1, u3ehi4]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1314, h1475, h1481, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1490_1]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1475, hlam, p1490_1]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [hlam, p1490_0]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1487, h1488, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1490_1, u3ehi4]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1314, h1475, h1481, h1489, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1490_1, u3ehi4]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1314, h1475, h1481, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1490_1]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1478, hlam, p1490_1]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1482, hlam, p1490_1]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [hlam, p1490_0]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1489, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1490_1, u3ehi4]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1314, h1475, h1481, h1482, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1490_1]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1479, hlam, p1490_1]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1483, hlam, p1490_0]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1486, hlam, p1490_0]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [hlam, p1490_0]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1486, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1490_1]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1480, hlam, p1490_0]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1485, hlam, p1490_0]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1488, hlam, p1490_0]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [h1489, hlam, p1490_0]
                              · have p1490_0 := h1490c.1
                                have p1490_1 := h1490c.2.1
                                have p1490_2 := h1490c.2.2.1
                                have p1490_3 := h1490c.2.2.2
                                linarith only [hlam, p1490_0]
                            · linarith only [h1314, h1475, h1480, h1481, h1489, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · linarith only [h1314, h1475, h1481, h1485, h1488, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h1486, h1487, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1314, h1475, h1481, h1483, h1486, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h1314, h1475, h1480, h1481, h1483, h1485, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                  · linarith only [h1314, h1475, h1483, h1484, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1314, h1475, h1479, h1483, hlam]
              · linarith only [h0, h1478, h1482, hlam]
            · linarith only [h0, h1477, h1481, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1525 | h1525
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1526 | h1526
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1527 | h1527
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1528 | h1528
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1529 | h1529
                    · linarith only [h1314, h1475, h1480, h1529, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1531 | h1531
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1532 | h1532
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1533 | h1533
                          · linarith only [h1475, h1480, h1526, h1533, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1535 | h1535
                            · linarith only [h1475, h1480, h1526, h1531, h1535, hlam]
                            · rcases h4bigk with h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c | h1537c
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1526, h1531, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p1537_1, u3ehi3]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1480, h1531, hc45, hlam, hphi, ht34, p1537_1, u3ehi3]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1480, hc45, hlam, hphi, ht34, p1537_1, u3ehi3]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1480, hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1475, hlam, p1537_1]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1314, h1476, h1525, h1529, h1531, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1537_1, u3ehi3]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1314, h1476, h1525, h1529, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1537_1, u3ehi3]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1529, hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1478, hlam, p1537_1]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1526, hlam, p1537_1]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1537_1, u3ehi3]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1533, hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1479, hlam, p1537_1]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1527, hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1531, hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1535, hlam, p1537_0]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [hc04, hc45, hlam, hphi, p1537_1]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [hc14, hc45, hlam, hphi, p1537_1]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [h1531, hc45, hlam, hphi, ht34, p1537_1, u3ehi3]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [hc45, hlam, hphi, ht34, p1537_1, u3ehi3]
                              · have p1537_0 := h1537c.1
                                have p1537_1 := h1537c.2.1
                                have p1537_2 := h1537c.2.2.1
                                have p1537_3 := h1537c.2.2.2
                                linarith only [hlam, p1537_0]
                        · linarith only [h1314, h1476, h1525, h1528, h1532, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · linarith only [h1479, h1480, h1531, hc45, hlam, hphi, ht34, u3ehi2]
                  · linarith only [h1314, h1475, h1527, h1528, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1314, h1479, h1527, hlam]
              · linarith only [h1314, h1476, h1478, h1479, h1480, h1525, h1526, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
            · linarith only [h0, h1477, h1525, hlam]
        · linarith only [h1314, h1475, h1479, hlam]
      · linarith only [h0, h1475, h1478, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1571 | h1571
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1572 | h1572
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1573 | h1573
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1574 | h1574
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1575 | h1575
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1576 | h1576
                · linarith only [h0, h1475, h1477, h1574, h1576, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h1475, h1477, h1572, h1574, h1576, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1475, h1477, h1572, h1574, h1575, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1580 | h1580
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1581 | h1581
                · linarith only [h0, h1475, h1574, h1581, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h1314, h1475, h1572, h1581, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1475, h1571, h1572, h1580, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1585 | h1585
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1586 | h1586
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1587 | h1587
                · linarith only [h0, h1475, h1477, h1585, h1587, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h1572, h1573, h1587, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h0, h1477, h1585, h1586, hc01, hc24, hlam, hphi, ht12]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1591 | h1591
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1592 | h1592
                · linarith only [h0, h1475, h1585, h1592, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h1314, h1475, h1572, h1592, hlam]
              · linarith only [h0, h1476, h1571, h1572, h1573, h1591, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
        · linarith only [h0, h1475, h1477, h1572, hlam]
      · linarith only [h0, h1475, h1571, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h1598 | h1598
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1599 | h1599
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1600 | h1600
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1601 | h1601
          · linarith only [h1475, h1476, h1601, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1603 | h1603
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1604 | h1604
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1605 | h1605
                · rcases m.htr 1 3 5 (by decide) (by decide) with h1606 | h1606
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h1607 | h1607
                    · linarith only [h1475, h1476, h1601, h1603, h1606, h1607, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h1475, h1476, h1605, h1607, hc45, hlam, hphi, ht34, u3ehi3]
                  · linarith only [h1314, h1475, h1605, h1606, hc35, hlam, hphi, u3ehi3]
                · linarith only [h1314, h1475, h1600, h1604, h1605, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1599, h1604, hlam]
            · linarith only [h0, h1598, h1603, hlam]
        · linarith only [h1314, h1475, h1600, hlam]
      · linarith only [h0, h1475, h1599, hlam]
    · rcases m.htr 0 2 4 (by decide) (by decide) with h1616 | h1616
      · rcases m.htr 0 3 4 (by decide) (by decide) with h1617 | h1617
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1618 | h1618
          · linarith only [h1475, h1476, h1618, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1620 | h1620
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1621 | h1621
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1622 | h1622
                · linarith only [h0, h1475, h1598, h1620, h1622, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h1475, h1598, h1617, h1620, h1622, hc03, hc14, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h0, h1475, h1598, h1617, h1620, h1621, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1626 | h1626
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1627 | h1627
                · linarith only [h0, h1475, h1620, h1627, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h1617, h1618, h1627, hc45, hlam, hphi, ht34, u3ehi1]
              · linarith only [h0, h1475, h1616, h1626, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
        · linarith only [h0, h1475, h1598, h1617, hlam]
      · linarith only [h0, h1475, h1616, hlam]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_13_24_L_R_H_I_x1_x1_x1_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1314 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1475 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1633 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
  have hc03 := m.hcor 0 3 (by decide)
  have hc04 := m.hcor 0 4 (by decide)
  have hc12 := m.hcor 1 2 (by decide)
  have hc13 := m.hcor 1 3 (by decide)
  have hc14 := m.hcor 1 4 (by decide)
  have hc15 := m.hcor 1 5 (by decide)
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
  have h3ehi := hb3.1
  have h4bigk := hb4.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1634 | h1634
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1635 | h1635
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1636 | h1636
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1637 | h1637
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1638 | h1638
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1639 | h1639
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1640 | h1640
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1641 | h1641
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1642 | h1642
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1643 | h1643
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1644 | h1644
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1645 | h1645
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1646 | h1646
                          · rcases h4bigk with h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c | h1647c
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [hlam, p1647_0]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [h1475, hlam, p1647_0]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [h1475, h1638, h1640, h1643, h1646, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1647_1, u3ehi4]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [h1475, h1638, h1640, h1646, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1647_1, u3ehi4]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              rcases p1647_3 (m.d 0 4) (by simp) with h1652 | h1652
                              · rcases p1647_3 (m.d 1 4) (by simp) with h1653 | h1653
                                · rcases p1647_3 (m.d 2 4) (by simp) with h1654 | h1654
                                  · linarith only [h1635, h1654, hlam]
                                  · linarith only [h1645, h1654, hlam]
                                · linarith only [h1642, h1653, hlam]
                              · linarith only [h1652, hlam, p1647_0]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [h1475, h1638, h1640, hc01, hc12, hlam, hphi, p1647_1]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [hlam, p1647_0]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [h1638, h1640, h1643, h1646, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1647_1, u3ehi4]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [h1638, h1640, h1646, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1647_1, u3ehi4]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              rcases p1647_3 (m.d 0 4) (by simp) with h1663 | h1663
                              · linarith only [h1475, h1663, hlam]
                              · linarith only [h1637, h1663, hlam]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [h1635, hlam, p1647_1]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [h1639, hlam, p1647_1]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [hlam, p1647_0]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [h1646, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1647_1, u3ehi4]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [h0, h1634, h1643, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p1647_1]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [h1636, hlam, p1647_1]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [h1640, hlam, p1647_0]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [h1643, hlam, p1647_0]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [hlam, p1647_0]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [h1636, hc03, hc45, hlam, hphi, ht0b, ht5b, p1647_1]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [h1637, hlam, p1647_0]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [h1642, hlam, p1647_0]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [h1645, hlam, p1647_0]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [h1646, hlam, p1647_0]
                            · have p1647_0 := h1647c.1
                              have p1647_1 := h1647c.2.1
                              have p1647_2 := h1647c.2.2.1
                              have p1647_3 := h1647c.2.2.2
                              linarith only [hlam, p1647_0]
                          · linarith only [h1475, h1633, h1638, h1640, h1642, h1646, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h1475, h1633, h1638, h1640, h1642, h1643, h1645, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1475, h1633, h1638, h1640, h1641, h1644, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1684 | h1684
                      · linarith only [h1643, h1684, hc34, hlam, hphi, u3ehi4]
                      · linarith only [h1475, h1633, h1638, h1640, h1641, h1684, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h1475, h1633, h1641, h1642, hc45, hlam, hphi, ht34, u3ehi4]
                · linarith only [h1314, h1636, h1641, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1314, h1636, h1640, hlam]
            · linarith only [h0, h1635, h1639, hlam]
          · linarith only [h0, h1634, h1638, hlam]
        · linarith only [h1475, h1633, h1637, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1693 | h1693
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1694 | h1694
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1695 | h1695
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1696 | h1696
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1697 | h1697
                · linarith only [h1314, h1633, h1636, h1694, h1696, h1697, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h1314, h1636, h1696, h1697, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1700 | h1700
                · linarith only [h1696, h1700, hc34, hlam, hphi, u3ehi4]
                · linarith only [h1314, h1633, h1700, hlam]
            · linarith only [h0, h1635, h1695, hlam]
          · linarith only [h0, h1634, h1694, hlam]
        · linarith only [h1314, h1633, h1636, h1693, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1706 | h1706
      · linarith only [h1634, h1635, h1706, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1708 | h1708
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1709 | h1709
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1710 | h1710
            · linarith only [h1634, h1635, h1710, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1712 | h1712
              · linarith only [h1314, h1706, h1709, h1710, h1712, hc01, hc24, hlam, hphi, ht12]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1714 | h1714
                · linarith only [h1712, h1714, hc34, hlam, hphi, u3ehi4]
                · linarith only [h0, h1633, h1710, h1714, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h1633, h1634, h1635, h1709, hc04, hc15, hlam, hphi, ht0b, ht5b]
        · linarith only [h1634, h1635, h1708, hc45, hlam, hphi, ht34, u3ehi2]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h1719 | h1719
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1720 | h1720
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1721 | h1721
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1722 | h1722
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1723 | h1723
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1724 | h1724
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1725 | h1725
                · linarith only [h0, h1633, h1634, h1722, h1725, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h1314, h1720, h1725, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1634, h1719, h1720, h1722, h1724, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
            · linarith only [h1634, h1719, h1720, h1722, h1723, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1730 | h1730
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1731 | h1731
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1732 | h1732
                · linarith only [h0, h1633, h1722, h1732, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h1314, h1720, h1732, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1314, h1720, h1731, hlam]
            · linarith only [h0, h1633, h1719, h1730, hc02, hc15, hlam, hphi, ht0b, ht5b]
        · linarith only [h1475, h1633, h1721, hlam]
      · linarith only [h1634, h1719, h1720, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h1739 | h1739
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1740 | h1740
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1741 | h1741
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1742 | h1742
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1743 | h1743
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1744 | h1744
                · linarith only [h0, h1633, h1634, h1741, h1744, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h1314, h1739, h1744, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1634, h1739, h1741, h1743, hlam]
            · linarith only [h1634, h1739, h1741, h1742, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1749 | h1749
            · linarith only [h0, h1719, h1741, h1749, hc01, hc23, hlam, hphi, ht12]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1751 | h1751
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1752 | h1752
                · linarith only [h0, h1633, h1741, h1752, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h1314, h1739, h1752, hc35, hlam, hphi, u3ehi3]
              · linarith only [h1314, h1739, h1751, hlam]
        · linarith only [h1475, h1633, h1740, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1757 | h1757
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1758 | h1758
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1759 | h1759
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1760 | h1760
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1761 | h1761
                · linarith only [h1314, h1633, h1739, h1758, h1760, h1761, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h0, h1634, h1739, h1760, h1761, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1764 | h1764
                · linarith only [h1760, h1764, hc34, hlam, hphi, u3ehi4]
                · linarith only [h0, h1633, h1634, h1758, h1764, hlam]
            · linarith only [h0, h1633, h1634, h1758, h1759, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1768 | h1768
            · linarith only [h0, h1633, h1719, h1758, h1768, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h1770 | h1770
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1771 | h1771
                · linarith only [h0, h1633, h1758, h1771, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h0, h1634, h1739, h1770, h1771, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h1774 | h1774
                · linarith only [h1770, h1774, hc34, hlam, hphi, u3ehi4]
                · linarith only [h0, h1633, h1758, h1774, hlam]
        · linarith only [h0, h1633, h1634, h1739, h1757, hlam]

end R2N4
