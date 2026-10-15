import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_54S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4472000 in
theorem r1l7_11_23_L_I_M_LI_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h939 | h939
  · rcases m.htr 1 2 4 (by decide) (by decide) with h940 | h940
    · rcases m.htr 1 2 5 (by decide) (by decide) with h941 | h941
      · rcases m.htr 1 3 4 (by decide) (by decide) with h942 | h942
        · rcases m.htr 1 3 5 (by decide) (by decide) with h943 | h943
          · linarith only [h4, h943, hc03, hlam, hphi, u3elo1]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h945 | h945
            · linarith only [h942, h943, h945, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h947 | h947
              · rcases m.htr 2 3 5 (by decide) (by decide) with h948 | h948
                · linarith only [h3, h4, h939, h943, h948, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h950 | h950
                  · linarith only [h940, h945, h950, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h952 | h952
                    · linarith only [h941, h945, h947, h948, h952, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases h1bigk with h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c | h954c
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [hlam, p954_0]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [h939, h947, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p954_1]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        rcases p954_3 (m.d 0 1) (by simp) with h957 | h957
                        · rcases p954_3 (m.d 1 2) (by simp) with h958 | h958
                          · linarith only [h0, h958, hlam]
                          · linarith only [h939, h958, hlam]
                        · linarith only [h957, hlam, p954_0]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        rcases p954_3 (m.d 0 1) (by simp) with h962 | h962
                        · rcases p954_3 (m.d 1 2) (by simp) with h963 | h963
                          · linarith only [h0, h963, hlam]
                          · linarith only [h940, h963, hlam]
                        · linarith only [h962, hlam, p954_0]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        rcases p954_3 (m.d 0 1) (by simp) with h967 | h967
                        · rcases p954_3 (m.d 1 2) (by simp) with h968 | h968
                          · linarith only [h0, h968, hlam]
                          · linarith only [h941, h968, hlam]
                        · linarith only [h967, hlam, p954_0]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [h0, hlam, p954_0]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [hlam, p954_0]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [h0, h939, h947, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p954_1]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        rcases p954_3 (m.d 0 1) (by simp) with h975 | h975
                        · rcases p954_3 (m.d 1 2) (by simp) with h976 | h976
                          · rcases p954_3 (m.d 1 3) (by simp) with h977 | h977
                            · linarith only [h939, h977, hlam]
                            · linarith only [h942, h977, hlam]
                          · linarith only [h940, h976, hlam]
                        · linarith only [h2, h975, hlam]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [h0, h939, h943, h947, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p954_1]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [h1, hlam, p954_0]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [h939, hlam, p954_1]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [hlam, p954_0]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [h1, h4, hc14, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p954_1, u3elo4]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [h943, hlam, p954_1]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [h2, hlam, p954_0]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [h940, hlam, p954_1]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [h942, hlam, p954_0]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [hlam, p954_0]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [h945, hlam, p954_1]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [h3, hlam, p954_0]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [h941, hlam, p954_1]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [h3, h4, hc13, hlam, hphi, p954_1, u3elo4]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        rcases p954_3 (m.d 0 1) (by simp) with h996 | h996
                        · rcases p954_3 (m.d 1 2) (by simp) with h997 | h997
                          · rcases p954_3 (m.d 1 3) (by simp) with h998 | h998
                            · linarith only [h943, h998, hlam]
                            · linarith only [h942, h998, hlam]
                          · linarith only [h940, h997, hlam]
                        · linarith only [h2, h996, hlam]
                      · have p954_0 := h954c.1
                        have p954_1 := h954c.2.1
                        have p954_2 := h954c.2.2.1
                        have p954_3 := h954c.2.2.2
                        linarith only [hlam, p954_0]
              · linarith only [h942, h947, hc23, hlam, hphi, u3elo1]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1005 | h1005
          · linarith only [h1, h1005, h4, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1007 | h1007
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1008 | h1008
              · linarith only [h1008, h942, hc13, hlam, hphi, u3elo2]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1010 | h1010
                · linarith only [h1010, h4, h939, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1012 | h1012
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1013 | h1013
                    · rcases h1bigk with h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c | h1014c
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [hlam, p1014_0]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [h1012, h940, hc01, hc45, hlam, hphi, ht0b, ht5b, p1014_1]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        rcases p1014_3 (m.d 0 1) (by simp) with h1017 | h1017
                        · rcases p1014_3 (m.d 1 2) (by simp) with h1018 | h1018
                          · linarith only [h0, h1018, hlam]
                          · linarith only [h1018, h939, hlam]
                        · linarith only [h1017, hlam, p1014_0]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        rcases p1014_3 (m.d 0 1) (by simp) with h1022 | h1022
                        · rcases p1014_3 (m.d 1 2) (by simp) with h1023 | h1023
                          · linarith only [h0, h1023, hlam]
                          · linarith only [h1023, h940, hlam]
                        · linarith only [h1022, hlam, p1014_0]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        rcases p1014_3 (m.d 0 1) (by simp) with h1027 | h1027
                        · rcases p1014_3 (m.d 1 2) (by simp) with h1028 | h1028
                          · linarith only [h0, h1028, hlam]
                          · linarith only [h1028, h941, hlam]
                        · linarith only [h1027, hlam, p1014_0]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [h0, hlam, p1014_0]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [hlam, p1014_0]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        rcases p1014_3 (m.d 0 1) (by simp) with h1034 | h1034
                        · rcases p1014_3 (m.d 1 2) (by simp) with h1035 | h1035
                          · rcases p1014_3 (m.d 1 3) (by simp) with h1036 | h1036
                            · linarith only [h1036, h939, hlam]
                            · rcases p1014_3 (m.d 1 4) (by simp) with h1038 | h1038
                              · linarith only [h1038, h940, hlam]
                              · linarith only [h1038, h942, hlam]
                          · linarith only [h1035, h939, hlam]
                        · linarith only [h1, h1034, hlam]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [h0, h1012, h940, hc01, hc45, hlam, hphi, ht0b, ht5b, p1014_1]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        rcases p1014_3 (m.d 0 1) (by simp) with h1044 | h1044
                        · rcases p1014_3 (m.d 1 2) (by simp) with h1045 | h1045
                          · rcases p1014_3 (m.d 1 3) (by simp) with h1046 | h1046
                            · linarith only [h1046, h939, hlam]
                            · rcases p1014_3 (m.d 1 4) (by simp) with h1048 | h1048
                              · linarith only [h1048, h940, hlam]
                              · linarith only [h1007, h1048, hlam]
                          · linarith only [h1045, h941, hlam]
                        · linarith only [h1044, h3, hlam]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [h1, hlam, p1014_0]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [h939, hlam, p1014_1]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [hlam, p1014_0]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [h942, hlam, p1014_1]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [h1005, hlam, p1014_1]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [h2, hlam, p1014_0]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [h940, hlam, p1014_1]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [h942, hc13, hlam, hphi, p1014_1, u3elo3]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [hlam, p1014_0]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [h1005, h939, h942, hc23, hlam, hphi, p1014_1, u3elo3]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [h3, hlam, p1014_0]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [h941, hlam, p1014_1]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [h1013, h3, h4, h939, hc23, hlam, hphi, p1014_1, u3elo3]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [h1007, hlam, p1014_0]
                      · have p1014_0 := h1014c.1
                        have p1014_1 := h1014c.2.1
                        have p1014_2 := h1014c.2.2.1
                        have p1014_3 := h1014c.2.2.2
                        linarith only [hlam, p1014_0]
                    · linarith only [h0, h1012, h1013, h940, h942, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h1007, h1008, h1012, h942, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1070 | h1070
              · linarith only [h1070, h939, h942, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1072 | h1072
                · linarith only [h1072, h4, h939, hc03, hlam, hphi, u3elo1]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h1074 | h1074
                  · linarith only [h1007, h1074, h940, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h1076 | h1076
                    · linarith only [h1007, h1076, h942, hc13, hlam, hphi, u3elo3]
                    · rcases h1bigk with h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c | h1078c
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        linarith only [hlam, p1078_0]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        rcases p1078_3 (m.d 0 1) (by simp) with h1080 | h1080
                        · rcases p1078_3 (m.d 1 2) (by simp) with h1081 | h1081
                          · linarith only [h1081, hlam, p1078_0]
                          · rcases p1078_3 (m.d 1 3) (by simp) with h1083 | h1083
                            · linarith only [h1, h1083, hlam]
                            · rcases p1078_3 (m.d 1 4) (by simp) with h1085 | h1085
                              · linarith only [h1085, h2, hlam]
                              · rcases p1078_3 (m.d 1 5) (by simp) with h1087 | h1087
                                · linarith only [h1087, h3, hlam]
                                · rcases h1emin with h1089 | h1089 | h1089 | h1089 | h1089
                                  · rcases h3bigk with h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c | h1090c
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [hlam, p1090_0]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [h4, h939, hc23, hlam, hphi, p1090_1, u3elo4]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [h4, hc23, hlam, hphi, p1090_1, u3elo4]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [h4, h939, h942, hc23, hlam, hphi, p1090_1, u3elo4]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [h4, hlam, p1090_0]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [h1, hlam, p1090_0]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [hlam, p1090_0]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [h942, hc23, hlam, hphi, p1090_1, u3elo3]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [h942, hlam, p1090_0]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [h1005, hlam, p1090_0]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [hc03, hlam, hphi, p1090_1, u3elo2]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [h939, hlam, p1090_0]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [hlam, p1090_0]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [h1070, hlam, p1090_0]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [h1072, hlam, p1090_0]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [h1076, hc03, hc45, hlam, hphi, ht34, p1090_1]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [h1076, h939, hc23, hc45, hlam, hphi, ht34, p1090_1]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [h1076, hc23, hc45, hlam, hphi, ht34, p1090_1]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [hlam, p1090_0]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [h1076, hlam, p1090_1]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [h1, h939, hc23, hlam, hphi, p1090_1, u3elo4]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [h939, hc23, hlam, hphi, p1090_1, u3elo4]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [hc23, hlam, hphi, p1090_1, u3elo4]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [h939, h942, hc23, hlam, hphi, p1090_1, u3elo4]
                                    · have p1090_0 := h1090c.1
                                      have p1090_1 := h1090c.2.1
                                      have p1090_2 := h1090c.2.2.1
                                      have p1090_3 := h1090c.2.2.2
                                      linarith only [hlam, p1090_0]
                                  · linarith only [h1089, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1078_1]
                                  · linarith only [h1, h1089, hlam, ht12, ht23, u3elo0]
                                  · linarith only [h1007, h1089, h3, h4, hlam, ht12, ht23, u3elo4]
                                  · linarith only [h1089, h3, h4, hlam, ht12, ht23, u3elo4]
                        · linarith only [h1080, hlam, p1078_0]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        rcases p1078_3 (m.d 0 1) (by simp) with h1121 | h1121
                        · rcases p1078_3 (m.d 1 2) (by simp) with h1122 | h1122
                          · linarith only [h0, h1122, hlam]
                          · linarith only [h1122, h939, hlam]
                        · linarith only [h1121, hlam, p1078_0]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        rcases p1078_3 (m.d 0 1) (by simp) with h1126 | h1126
                        · rcases p1078_3 (m.d 1 2) (by simp) with h1127 | h1127
                          · linarith only [h0, h1127, hlam]
                          · linarith only [h1127, h940, hlam]
                        · linarith only [h1126, hlam, p1078_0]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        rcases p1078_3 (m.d 0 1) (by simp) with h1131 | h1131
                        · rcases p1078_3 (m.d 1 2) (by simp) with h1132 | h1132
                          · linarith only [h0, h1132, hlam]
                          · linarith only [h1132, h941, hlam]
                        · linarith only [h1131, hlam, p1078_0]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        linarith only [h0, hlam, p1078_0]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        linarith only [hlam, p1078_0]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        rcases p1078_3 (m.d 0 1) (by simp) with h1138 | h1138
                        · rcases p1078_3 (m.d 1 2) (by simp) with h1139 | h1139
                          · rcases p1078_3 (m.d 1 3) (by simp) with h1140 | h1140
                            · linarith only [h1140, h939, hlam]
                            · rcases p1078_3 (m.d 1 4) (by simp) with h1142 | h1142
                              · linarith only [h1142, h940, hlam]
                              · linarith only [h1142, h942, hlam]
                          · linarith only [h1139, h939, hlam]
                        · linarith only [h1, h1138, hlam]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        rcases p1078_3 (m.d 0 1) (by simp) with h1147 | h1147
                        · rcases p1078_3 (m.d 1 2) (by simp) with h1148 | h1148
                          · rcases p1078_3 (m.d 1 3) (by simp) with h1149 | h1149
                            · linarith only [h1149, h939, hlam]
                            · rcases p1078_3 (m.d 1 4) (by simp) with h1151 | h1151
                              · linarith only [h1151, h940, hlam]
                              · rcases p1078_3 (m.d 1 5) (by simp) with h1153 | h1153
                                · linarith only [h1153, h941, hlam]
                                · linarith only [h1007, h1153, hlam]
                          · linarith only [h1148, h940, hlam]
                        · linarith only [h1147, h2, hlam]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        rcases p1078_3 (m.d 0 1) (by simp) with h1158 | h1158
                        · rcases p1078_3 (m.d 1 2) (by simp) with h1159 | h1159
                          · rcases p1078_3 (m.d 1 3) (by simp) with h1160 | h1160
                            · linarith only [h1160, h939, hlam]
                            · rcases p1078_3 (m.d 1 4) (by simp) with h1162 | h1162
                              · linarith only [h1162, h940, hlam]
                              · rcases p1078_3 (m.d 1 5) (by simp) with h1164 | h1164
                                · linarith only [h1164, h941, hlam]
                                · rcases h1emin with h1166 | h1166 | h1166 | h1166 | h1166
                                  · rcases h3bigk with h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c | h1167c
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [hlam, p1167_0]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [h4, h939, hc23, hlam, hphi, p1167_1, u3elo4]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [h4, hc23, hlam, hphi, p1167_1, u3elo4]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [h4, h939, h942, hc23, hlam, hphi, p1167_1, u3elo4]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [h4, hlam, p1167_0]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [h1, hlam, p1167_0]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [hlam, p1167_0]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [h1007, h942, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1078_1, p1167_1]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [h942, hlam, p1167_0]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [h1005, hlam, p1167_0]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [hc03, hlam, hphi, p1167_1, u3elo2]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [h939, hlam, p1167_0]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [hlam, p1167_0]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [h1070, hlam, p1167_0]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [h1072, hlam, p1167_0]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [h1076, hc03, hc45, hlam, hphi, ht34, p1167_1]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [h1076, h939, hc23, hc45, hlam, hphi, ht34, p1167_1]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [h1076, hc23, hc45, hlam, hphi, ht34, p1167_1]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [hlam, p1167_0]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [h1076, hlam, p1167_1]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [h1, h939, hc23, hlam, hphi, p1167_1, u3elo4]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [h939, hc23, hlam, hphi, p1167_1, u3elo4]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [hc23, hlam, hphi, p1167_1, u3elo4]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [h939, h942, hc23, hlam, hphi, p1167_1, u3elo4]
                                    · have p1167_0 := h1167c.1
                                      have p1167_1 := h1167c.2.1
                                      have p1167_2 := h1167c.2.2.1
                                      have p1167_3 := h1167c.2.2.2
                                      linarith only [hlam, p1167_0]
                                  · rcases h3bigk with h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c | h1193c
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [hlam, p1193_0]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [h939, hc23, hlam, hphi, p1193_1, u3elo0]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [h4, hc23, hlam, hphi, p1193_1, u3elo4]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [h4, h939, h942, hc23, hlam, hphi, p1193_1, u3elo4]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [h4, hlam, p1193_0]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [h1, hlam, p1193_0]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [hlam, p1193_0]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [h942, hc23, hlam, hphi, p1193_1, u3elo3]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [h942, hlam, p1193_0]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [h1005, hlam, p1193_0]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [hc03, hlam, hphi, p1193_1, u3elo2]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [h939, hlam, p1193_0]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [hlam, p1193_0]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [h1070, hlam, p1193_0]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [h1072, hlam, p1193_0]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [h1076, hc03, hc45, hlam, hphi, ht34, p1193_1]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [h1076, h939, hc23, hc45, hlam, hphi, ht34, p1193_1]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [h1076, hc23, hc45, hlam, hphi, ht34, p1193_1]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [hlam, p1193_0]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [h1076, hlam, p1193_1]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [h1, h939, hc23, hlam, hphi, p1193_1, u3elo4]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [h939, hc23, hlam, hphi, p1193_1, u3elo4]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [hc23, hlam, hphi, p1193_1, u3elo4]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [h939, h942, hc23, hlam, hphi, p1193_1, u3elo4]
                                    · have p1193_0 := h1193c.1
                                      have p1193_1 := h1193c.2.1
                                      have p1193_2 := h1193c.2.2.1
                                      have p1193_3 := h1193c.2.2.2
                                      linarith only [hlam, p1193_0]
                                  · linarith only [h1, h1166, hlam, ht12, ht23, u3elo0]
                                  · linarith only [h0, h1007, h1166, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1078_1]
                                  · linarith only [h0, h1166, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, p1078_1]
                          · linarith only [h1159, h941, hlam]
                        · linarith only [h1158, h3, hlam]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        linarith only [h1, hlam, p1078_0]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        linarith only [h939, hlam, p1078_1]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        linarith only [hlam, p1078_0]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        linarith only [h942, hlam, p1078_1]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        linarith only [h1005, hlam, p1078_1]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        linarith only [h2, hlam, p1078_0]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        linarith only [h940, hlam, p1078_1]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        linarith only [h1007, h3, h4, hc13, hlam, hphi, p1078_1, u3elo4]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        linarith only [hlam, p1078_0]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        linarith only [h1007, hlam, p1078_1]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        linarith only [h3, hlam, p1078_0]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        linarith only [h941, hlam, p1078_1]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        linarith only [h3, h4, h939, hc23, hlam, hphi, p1078_1, u3elo4]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        linarith only [h3, h4, h939, h942, hc23, hlam, hphi, p1078_1, u3elo4]
                      · have p1078_0 := h1078c.1
                        have p1078_1 := h1078c.2.1
                        have p1078_2 := h1078c.2.2.1
                        have p1078_3 := h1078c.2.2.2
                        linarith only [hlam, p1078_0]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1239 | h1239
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1240 | h1240
          · linarith only [h1, h1240, h4, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1242 | h1242
            · linarith only [h1242, h940, h941, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1244 | h1244
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1245 | h1245
                · linarith only [h1245, h4, hc03, hlam, hphi, u3elo2]
                · linarith only [h1244, h1245, h939, h941, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
              · linarith only [h1, h1239, h1244, hc23, hlam, hphi, u3elo0]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1249 | h1249
          · linarith only [h1, h1249, h4, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1251 | h1251
            · linarith only [h1251, h940, h941, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1253 | h1253
              · linarith only [h1239, h1253, h939, h941, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1255 | h1255
                · linarith only [h1255, h4, h939, hc03, hlam, hphi, u3elo1]
                · linarith only [h1253, h1255, h940, h941, hc23, hlam, hphi, u3elo4]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1258 | h1258
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1259 | h1259
        · linarith only [h1, h1259, h4, h939, h940, hc23, hlam, hphi, u3elo4]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1261 | h1261
          · linarith only [h1, h1261, h4, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1263 | h1263
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1264 | h1264
              · linarith only [h1259, h1264, h939, h940, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · linarith only [h1264, h939, h940, hc23, hlam, hphi, u3elo3]
            · linarith only [h1258, h1263, h940, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1268 | h1268
        · linarith only [h1, h1268, h4, h939, h940, hc23, hlam, hphi, u3elo4]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1270 | h1270
          · linarith only [h1, h1270, h4, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1272 | h1272
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1273 | h1273
              · linarith only [h1268, h1273, h939, h940, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
              · linarith only [h1273, h939, h940, hc23, hlam, hphi, u3elo3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1276 | h1276
              · linarith only [h1272, h1276, h939, h940, hc34, hc45, hlam, hphi]
              · linarith only [h1276, h939, h940, hc23, hlam, hphi, u3elo3]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1279 | h1279
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1280 | h1280
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1281 | h1281
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1282 | h1282
          · linarith only [h1, h1282, h4, hlam]
          · linarith only [h1280, h1282, h939, hlam]
        · linarith only [h1279, h1281, h939, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1286 | h1286
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1287 | h1287
          · linarith only [h1, h1287, h4, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1289 | h1289
            · linarith only [h1279, h1287, h1289, h939, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1291 | h1291
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1292 | h1292
                · linarith only [h1, h1279, h1291, h1292, h4, h939, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo2]
                · linarith only [h1279, h1291, h1292, h939, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
              · linarith only [h1279, h1291, h939, hc24, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo3]
        · linarith only [h1279, h1286, h939, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1297 | h1297
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1298 | h1298
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1299 | h1299
          · linarith only [h1299, h4, hc03, hlam, hphi, u3elo1]
          · linarith only [h1297, h1299, h939, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1302 | h1302
          · linarith only [h1298, h1302, h4, hc03, hlam, hphi, u3elo3]
          · linarith only [h1297, h1302, h939, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1305 | h1305
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1306 | h1306
          · linarith only [h1, h1306, h4, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1308 | h1308
            · linarith only [h1305, h1306, h1308, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1310 | h1310
              · rcases m.htr 2 3 5 (by decide) (by decide) with h1311 | h1311
                · linarith only [h1311, h4, hc03, hlam, hphi, u3elo2]
                · linarith only [h1311, h939, hc12, hlam, hphi, ht23, u3elo4]
              · linarith only [h1310, h939, hc12, hlam, hphi, ht23, u3elo3]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1315 | h1315
          · linarith only [h1, h1315, h4, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1317 | h1317
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1318 | h1318
              · linarith only [h1305, h1318, hc13, hlam, hphi, u3elo2]
              · linarith only [h1318, h939, hc12, hlam, hphi, ht23, u3elo3]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h1321 | h1321
              · linarith only [h1305, h1321, h939, hc12, hlam, hphi, ht23, u3elo2]
              · linarith only [h1321, h939, hc12, hlam, hphi, ht23, u3elo3]

set_option maxHeartbeats 4472000 in
theorem r1l7_11_23_L_I_M_LI_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h4 | h4
  · exact r1l7_11_23_L_I_M_LI_x0_x0_x0_x0_x0 m hb1 hb3 h0 h1 h2 h3 h4
  · exact r1l7_11_23_L_I_M_LI_x0_x0_x0_x0_x1 m hb1 hb3 h0 h1 h2 h3 h4

set_option maxHeartbeats 4472000 in
theorem r1l7_11_23_L_I_M_LI_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h1324 | h1324
  · linarith only [h1, h1324, h3, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1326 | h1326
    · linarith only [h0, h1324, h1326, h3, hc23, hlam, hphi, u3elo4]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1328 | h1328
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1329 | h1329
        · linarith only [h1, h1326, h1329, h3, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1331 | h1331
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1332 | h1332
            · linarith only [h1, h1324, h1332, h3, hlam]
            · linarith only [h1, h1326, h1332, h3, hc12, hlam, hphi, ht23, u3elo4]
          · linarith only [h1326, h1328, h1331, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1336 | h1336
        · linarith only [h0, h1336, h3, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1338 | h1338
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1339 | h1339
            · linarith only [h1, h1324, h1339, h3, hlam]
            · linarith only [h1, h1338, h1339, h3, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u3elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1342 | h1342
            · linarith only [h1324, h1338, h1342, hc03, hlam, hphi, u3elo3]
            · linarith only [h1326, h1338, h1342, h2, h3, hc12, hlam, hphi, ht23, u3elo4]

set_option maxHeartbeats 4472000 in
theorem r1l7_11_23_L_I_M_LI_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_11_23_L_I_M_LI_x0_x0_x0_x0 m hb1 hb3 h0 h1 h2 h3
  · exact r1l7_11_23_L_I_M_LI_x0_x0_x0_x1 m hb1 hb3 h0 h1 h2 h3

set_option maxHeartbeats 4472000 in
theorem r1l7_11_23_L_I_M_LI_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1345 | h1345
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1346 | h1346
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1347 | h1347
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1348 | h1348
        · linarith only [h0, h1348, h2, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1350 | h1350
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1351 | h1351
            · linarith only [h0, h1, h1347, h1351, h2, hc23, hlam, hphi, u3elo0]
            · linarith only [h0, h1347, h1351, h2, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1354 | h1354
            · linarith only [h1345, h1347, h1350, h1354, h2, hlam]
            · linarith only [h1345, h1347, h1350, h1354, h2, hc23, hlam, hphi, u3elo3]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1357 | h1357
        · linarith only [h0, h1357, h2, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1359 | h1359
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1360 | h1360
            · linarith only [h1, h1360, h2, hlam]
            · linarith only [h1, h1347, h1359, h1360, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1363 | h1363
            · linarith only [h1, h1363, h2, hlam]
            · linarith only [h1, h1347, h1363, h2, hc12, hlam, hphi, ht23, u3elo3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1366 | h1366
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1367 | h1367
        · linarith only [h0, h1367, h2, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1369 | h1369
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1370 | h1370
            · linarith only [h0, h1, h1346, h1366, h1370, h2, hc23, hlam, hphi, u3elo4]
            · linarith only [h0, h1366, h1370, h2, hc23, hlam, hphi, u3elo3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1373 | h1373
            · linarith only [h1, h1345, h1346, h1366, h1369, h1373, h2, hc23, hlam, hphi, u3elo4]
            · linarith only [h1345, h1366, h1369, h1373, h2, hc23, hlam, hphi, u3elo3]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1376 | h1376
        · linarith only [h1, h1346, h1366, h1376, h2, hc01, hlam, hphi, ht12, ht23, u3elo4]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1378 | h1378
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1379 | h1379
            · linarith only [h1, h1379, h2, hlam]
            · linarith only [h1, h1366, h1378, h1379, h2, hc25, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u3elo3]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1382 | h1382
            · linarith only [h1, h1382, h2, hlam]
            · linarith only [h1, h1366, h1382, h2, hc12, hlam, hphi, ht23, u3elo3]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h1385 | h1385
    · linarith only [h1, h1345, h1385, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1387 | h1387
      · linarith only [h0, h1345, h1385, h1387, hc23, hlam, hphi, u3elo4]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1389 | h1389
        · linarith only [h1, h1387, h1389, h2, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1391 | h1391
          · linarith only [h1, h1345, h1387, h1391, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1393 | h1393
            · linarith only [h1, h1393, h2, hlam]
            · linarith only [h1, h1387, h1393, h2, hc12, hlam, hphi, ht23, u3elo3]

set_option maxHeartbeats 4472000 in
theorem r1l7_11_23_L_I_M_LI_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_11_23_L_I_M_LI_x0_x0_x0 m hb1 hb3 h0 h1 h2
  · exact r1l7_11_23_L_I_M_LI_x0_x0_x1 m hb1 hb3 h0 h1 h2

set_option maxHeartbeats 4472000 in
theorem r1l7_11_23_L_I_M_LI_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  linarith only [h0, h1, hc12, hlam, hphi, ht23, u3elo1]

set_option maxHeartbeats 4472000 in
theorem r1l7_11_23_L_I_M_LI_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_M_LI m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h1emin := hb1.2.1
  have h3elo := hb3.1
  have h3bigk := hb3.2.2.2
  have u3elo0 := h3elo (m.d 0 3) (by simp)
  have u3elo1 := h3elo (m.d 1 3) (by simp)
  have u3elo2 := h3elo (m.d 2 3) (by simp)
  have u3elo3 := h3elo (m.d 3 4) (by simp)
  have u3elo4 := h3elo (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_23_L_I_M_LI_x0_x0 m hb1 hb3 h0 h1
  · exact r1l7_11_23_L_I_M_LI_x0_x1 m hb1 hb3 h0 h1

end R2N4
