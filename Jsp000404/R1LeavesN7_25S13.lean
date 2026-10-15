import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_25S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5040000 in
set_option maxHeartbeats 5040000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h930 | h930
  · rcases m.htr 0 4 5 (by decide) (by decide) with h931 | h931
    · rcases m.htr 1 2 3 (by decide) (by decide) with h932 | h932
      · rcases m.htr 1 2 4 (by decide) (by decide) with h933 | h933
        · rcases m.htr 1 2 5 (by decide) (by decide) with h934 | h934
          · rcases m.htr 1 3 4 (by decide) (by decide) with h935 | h935
            · linarith only [h1, h7, h930, h935, hc01, hc35, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h937 | h937
              · rcases m.htr 2 3 4 (by decide) (by decide) with h938 | h938
                · linarith only [h7, h930, h932, h938, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h940 | h940
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h941 | h941
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h942 | h942
                      · rcases h0bigk with h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c | h943c
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [hlam, p943_0]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [h4, h940, h942, hc01, hc45, hlam, hphi, ht0b, ht5b, p943_1]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [h1, h932, h940, h942, hc01, hc45, hlam, hphi, ht0b, ht5b, p943_1]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [h1, h7, h932, h940, h942, hc01, hc45, hlam, hphi, ht0b, ht5b, p943_1]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          rcases p943_3 (m.d 0 1) (by simp) with h948 | h948
                          · rcases p943_3 (m.d 0 2) (by simp) with h949 | h949
                            · linarith only [h0, h949, hlam]
                            · linarith only [h6, h949, hlam]
                          · linarith only [h3, h948, hlam]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [h0, hlam, p943_0]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [hlam, p943_0]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [h1, h932, h940, h942, hc02, hc45, hlam, hphi, ht0b, ht5b, p943_1]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [h0, h1, h7, h932, h940, h942, hc01, hc45, hlam, hphi, ht0b, ht5b, p943_1]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          rcases p943_3 (m.d 0 1) (by simp) with h957 | h957
                          · rcases p943_3 (m.d 0 2) (by simp) with h958 | h958
                            · rcases p943_3 (m.d 0 3) (by simp) with h959 | h959
                              · linarith only [h4, h959, hlam]
                              · linarith only [h930, h959, hlam]
                            · linarith only [h6, h958, hlam]
                          · linarith only [h3, h957, hlam]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [h1, hlam, p943_1]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [h4, hlam, p943_1]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [hlam, p943_0]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [h7, hlam, p943_1]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [h7, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p943_1]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [h2, hlam, p943_0]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [h5, hlam, p943_0]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [h1, h932, h940, h942, hc04, hc45, hlam, hphi, ht0b, ht5b, p943_1]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [hlam, p943_0]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          rcases p943_3 (m.d 0 1) (by simp) with h973 | h973
                          · rcases p943_3 (m.d 0 2) (by simp) with h974 | h974
                            · rcases p943_3 (m.d 0 3) (by simp) with h975 | h975
                              · linarith only [h7, h975, hlam]
                              · linarith only [h930, h975, hlam]
                            · linarith only [h6, h974, hlam]
                          · linarith only [h3, h973, hlam]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [h3, hlam, p943_0]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [h6, hlam, p943_1]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [h930, hlam, p943_0]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [h931, hlam, p943_1]
                        · have p943_0 := h943c.1
                          have p943_1 := h943c.2.1
                          have p943_2 := h943c.2.2.1
                          have p943_3 := h943c.2.2.2
                          linarith only [hlam, p943_0]
                      · linarith only [h5, h7, h938, h940, h942, hc35, hlam, hphi, u5elo4]
                    · linarith only [h938, h940, h941, hc35, hlam, hphi, u5elo4]
                  · linarith only [h7, h930, h940, hc23, hc34, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h988 | h988
                · linarith only [h1, h7, h930, h931, h932, h937, h988, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h990 | h990
                  · linarith only [h931, h932, h935, h937, h990, hc35, hlam, hphi, u5elo0]
                  · linarith only [h7, h930, h990, hc23, hc34, hlam, hphi]
          · linarith only [h6, h932, h934, hc23, hlam, hphi, ht34, ht45, u5elo0]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h994 | h994
          · rcases m.htr 1 3 4 (by decide) (by decide) with h995 | h995
            · linarith only [h1, h7, h995, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h997 | h997
              · rcases m.htr 2 3 4 (by decide) (by decide) with h998 | h998
                · linarith only [h5, h7, h932, h933, h998, hc02, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1000 | h1000
                  · linarith only [h0, h1000, h5, h932, h933, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · linarith only [h1000, h7, h930, hc23, hc34, hlam, hphi]
              · linarith only [h933, h994, h997, hc25, hlam, hphi, u5elo4]
          · linarith only [h932, h994, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1005 | h1005
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1006 | h1006
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1007 | h1007
            · linarith only [h1005, h1007, h4, h7, h932, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
            · linarith only [h1005, h1007, h932, hlam]
          · linarith only [h1005, h1006, hc24, hlam, hphi, ht45, u5elo2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1011 | h1011
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1012 | h1012
            · linarith only [h1011, h1012, h4, h7, h932, hc13, hc25, hlam, hphi, ht01, ht0b, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1014 | h1014
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1015 | h1015
                · linarith only [h1015, h4, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1017 | h1017
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1018 | h1018
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1019 | h1019
                      · rcases h0bigk with h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c | h1020c
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [hlam, p1020_0]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [h0, h1011, h1017, h1019, hc01, hc45, hlam, hphi, ht0b, ht5b, p1020_1]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [h1011, h1017, h1019, h4, h932, hc01, hc45, hlam, hphi, ht0b, ht5b, p1020_1]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [h1011, h1017, h1019, h4, h7, h932, hc01, hc45, hlam, hphi, ht0b, ht5b, p1020_1]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          rcases p1020_3 (m.d 0 1) (by simp) with h1025 | h1025
                          · rcases p1020_3 (m.d 0 2) (by simp) with h1026 | h1026
                            · linarith only [h0, h1026, hlam]
                            · linarith only [h1026, h6, hlam]
                          · linarith only [h1025, h3, hlam]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [h0, hlam, p1020_0]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [hlam, p1020_0]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [h1011, h1017, h1019, h4, h932, hc02, hc45, hlam, hphi, ht0b, ht5b, p1020_1]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [h0, h1011, h1017, h1019, h4, h7, h932, hc01, hc45, hlam, hphi, ht0b, ht5b, p1020_1]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          rcases p1020_3 (m.d 0 1) (by simp) with h1034 | h1034
                          · rcases p1020_3 (m.d 0 2) (by simp) with h1035 | h1035
                            · rcases p1020_3 (m.d 0 3) (by simp) with h1036 | h1036
                              · linarith only [h1036, h4, hlam]
                              · linarith only [h1036, h930, hlam]
                            · linarith only [h1035, h6, hlam]
                          · linarith only [h1034, h3, hlam]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [h1, hlam, p1020_1]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [h4, hlam, p1020_1]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [hlam, p1020_0]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [h7, hlam, p1020_1]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [h7, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1020_1]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [h2, hlam, p1020_0]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [h5, hlam, p1020_0]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [h4, h932, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1020_1]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [hlam, p1020_0]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          rcases p1020_3 (m.d 0 1) (by simp) with h1050 | h1050
                          · rcases p1020_3 (m.d 0 2) (by simp) with h1051 | h1051
                            · rcases p1020_3 (m.d 0 3) (by simp) with h1052 | h1052
                              · linarith only [h1052, h7, hlam]
                              · linarith only [h1052, h930, hlam]
                            · linarith only [h1051, h6, hlam]
                          · linarith only [h1050, h3, hlam]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [h3, hlam, p1020_0]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [h6, hlam, p1020_1]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [h930, hlam, p1020_0]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [h931, hlam, p1020_1]
                        · have p1020_0 := h1020c.1
                          have p1020_1 := h1020c.2.1
                          have p1020_2 := h1020c.2.2.1
                          have p1020_3 := h1020c.2.2.2
                          linarith only [hlam, p1020_0]
                      · linarith only [h1019, h4, h7, h932, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h1011, h1014, h1015, h1017, h1018, h932, hc35, hlam, hphi, u5elo1]
                  · linarith only [h1011, h1017, h932, hc25, hlam, hphi, u5elo3]
              · linarith only [h1011, h1012, h1014, h932, hc25, hlam, hphi, u5elo4]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1066 | h1066
            · linarith only [h1, h1066, h7, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1068 | h1068
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1069 | h1069
                · linarith only [h1069, h4, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1071 | h1071
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1072 | h1072
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1073 | h1073
                      · rcases h0bigk with h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c | h1074c
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [hlam, p1074_0]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1074_1]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h1011, h6, h930, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1074_1]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h1011, h6, h7, h930, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1074_1]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h1011, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1074_1]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h0, hlam, p1074_0]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [hlam, p1074_0]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h1011, h6, h930, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1074_1]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h0, h1011, h6, h7, h930, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1074_1]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h0, h1011, h6, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1074_1]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h1, hlam, p1074_1]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h4, hlam, p1074_1]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [hlam, p1074_0]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h7, hlam, p1074_1]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h1011, h6, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1074_1]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h2, hlam, p1074_0]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h5, hlam, p1074_0]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h7, hc03, hc34, hlam, hphi, p1074_1]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [hlam, p1074_0]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h1011, h6, h7, hc12, hc34, hlam, hphi, ht23, p1074_1]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h3, hlam, p1074_0]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h6, hlam, p1074_1]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h930, hlam, p1074_0]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [h931, hlam, p1074_1]
                        · have p1074_0 := h1074c.1
                          have p1074_1 := h1074c.2.1
                          have p1074_2 := h1074c.2.2.1
                          have p1074_3 := h1074c.2.2.2
                          linarith only [hlam, p1074_0]
                      · linarith only [h1068, h1073, h2, h7, hlam]
                    · linarith only [h1005, h1068, h1072, hlam]
                  · linarith only [h1071, h7, h930, hc23, hc34, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1103 | h1103
                · linarith only [h0, h1103, h4, h7, h930, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1105 | h1105
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1106 | h1106
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1107 | h1107
                      · linarith only [h1066, h1068, h1107, h7, h930, h932, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1106, h1107, h7, hc03, hlam, hphi, ht34, ht45, u5elo2]
                    · linarith only [h1005, h1106, h931, hc12, hlam, hphi, ht23, ht34, ht45, u5elo0]
                  · linarith only [h1105, h932, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
    · linarith only [h7, h930, h931, hc35, hlam, hphi, u5elo4]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1113 | h1113
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1114 | h1114
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1115 | h1115
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1116 | h1116
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1117 | h1117
            · linarith only [h1, h1117, h930, hc34, hlam, hphi, ht45, u5elo3]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1119 | h1119
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1120 | h1120
                · linarith only [h1, h1114, h1120, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1122 | h1122
                  · linarith only [h1, h1114, h1122, h930, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1124 | h1124
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1125 | h1125
                      · rcases h0bigk with h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c | h1126c
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [hlam, p1126_0]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [h0, h1115, h1124, hc01, hc45, hlam, hphi, ht0b, ht5b, p1126_1]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          rcases p1126_3 (m.d 0 1) (by simp) with h1129 | h1129
                          · rcases p1126_3 (m.d 0 2) (by simp) with h1130 | h1130
                            · linarith only [h0, h1130, hlam]
                            · linarith only [h1130, h4, hlam]
                          · linarith only [h1, h1129, hlam]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [h1115, h1124, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p1126_1]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          rcases p1126_3 (m.d 0 1) (by simp) with h1135 | h1135
                          · rcases p1126_3 (m.d 0 2) (by simp) with h1136 | h1136
                            · linarith only [h0, h1136, hlam]
                            · linarith only [h1136, h6, hlam]
                          · linarith only [h1135, h3, hlam]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [h0, hlam, p1126_0]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [hlam, p1126_0]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          rcases p1126_3 (m.d 0 1) (by simp) with h1142 | h1142
                          · rcases p1126_3 (m.d 0 2) (by simp) with h1143 | h1143
                            · rcases p1126_3 (m.d 0 3) (by simp) with h1144 | h1144
                              · linarith only [h1144, h4, hlam]
                              · rcases p1126_3 (m.d 0 4) (by simp) with h1146 | h1146
                                · linarith only [h1146, h5, hlam]
                                · linarith only [h1146, h7, hlam]
                            · linarith only [h1143, h4, hlam]
                          · linarith only [h1, h1142, hlam]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [h1115, h1124, h2, hc02, hc45, hlam, hphi, ht0b, ht5b, p1126_1]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          rcases p1126_3 (m.d 0 1) (by simp) with h1152 | h1152
                          · rcases p1126_3 (m.d 0 2) (by simp) with h1153 | h1153
                            · rcases p1126_3 (m.d 0 3) (by simp) with h1154 | h1154
                              · linarith only [h1154, h4, hlam]
                              · rcases p1126_3 (m.d 0 4) (by simp) with h1156 | h1156
                                · linarith only [h1156, h5, hlam]
                                · linarith only [h1113, h1156, hlam]
                            · linarith only [h1153, h6, hlam]
                          · linarith only [h1152, h3, hlam]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [h1, hlam, p1126_1]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [h4, hlam, p1126_1]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [hlam, p1126_0]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [h7, hlam, p1126_1]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [h930, hlam, p1126_1]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [h2, hlam, p1126_0]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [h5, hlam, p1126_0]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [h7, hc03, hc34, hlam, hphi, p1126_1]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [hlam, p1126_0]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [h1, h1114, h7, h930, hc23, hc34, hlam, hphi, p1126_1]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [h3, hlam, p1126_0]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [h6, hlam, p1126_1]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [h1, h1114, hc23, hlam, hphi, ht34, ht45, p1126_1, u5elo0]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [h1113, hlam, p1126_1]
                        · have p1126_0 := h1126c.1
                          have p1126_1 := h1126c.2.1
                          have p1126_2 := h1126c.2.2.1
                          have p1126_3 := h1126c.2.2.2
                          linarith only [hlam, p1126_0]
                      · linarith only [h1115, h1124, h1125, h2, h7, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1177 | h1177
                      · rcases h0bigk with h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c | h1178c
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [hlam, p1178_0]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1178_1]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          rcases p1178_3 (m.d 0 1) (by simp) with h1181 | h1181
                          · rcases p1178_3 (m.d 0 2) (by simp) with h1182 | h1182
                            · linarith only [h0, h1182, hlam]
                            · linarith only [h1182, h4, hlam]
                          · linarith only [h1, h1181, hlam]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [h1119, h1120, h1124, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1178_1]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [h1113, h1120, h1124, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1178_1]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [h0, hlam, p1178_0]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [hlam, p1178_0]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          rcases p1178_3 (m.d 0 1) (by simp) with h1190 | h1190
                          · rcases p1178_3 (m.d 0 2) (by simp) with h1191 | h1191
                            · rcases p1178_3 (m.d 0 3) (by simp) with h1192 | h1192
                              · linarith only [h1192, h4, hlam]
                              · rcases p1178_3 (m.d 0 4) (by simp) with h1194 | h1194
                                · linarith only [h1194, h5, hlam]
                                · linarith only [h1194, h7, hlam]
                            · linarith only [h1191, h4, hlam]
                          · linarith only [h1, h1190, hlam]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [h1119, h1120, h1124, h2, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1178_1]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [h0, h1119, h1120, h1124, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1178_1]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [h1, hlam, p1178_1]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [h4, hlam, p1178_1]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [hlam, p1178_0]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [h7, hlam, p1178_1]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [h930, hlam, p1178_1]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [h2, hlam, p1178_0]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [h5, hlam, p1178_0]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [h1, h1114, h7, hc23, hc34, hlam, hphi, p1178_1]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [hlam, p1178_0]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [h1119, h1120, h1124, h3, h7, hc23, hc34, hlam, hphi, p1178_1]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [h3, hlam, p1178_0]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [h6, hlam, p1178_1]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [h1, h1114, hc23, hlam, hphi, ht34, ht45, p1178_1, u5elo0]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [h1113, hlam, p1178_1]
                        · have p1178_0 := h1178c.1
                          have p1178_1 := h1178c.2.1
                          have p1178_2 := h1178c.2.2.1
                          have p1178_3 := h1178c.2.2.2
                          linarith only [hlam, p1178_0]
                      · linarith only [h1119, h1177, h2, h7, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1217 | h1217
                · linarith only [h1113, h1114, h1117, h1119, h1217, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1219 | h1219
                  · linarith only [h1114, h1117, h1119, h1219, h930, hc05, hlam, hphi, u5elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1221 | h1221
                    · linarith only [h0, h1114, h1115, h1117, h1119, h1221, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1223 | h1223
                      · rcases h0bigk with h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c | h1224c
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [hlam, p1224_0]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1224_1]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          rcases p1224_3 (m.d 0 1) (by simp) with h1227 | h1227
                          · rcases p1224_3 (m.d 0 2) (by simp) with h1228 | h1228
                            · linarith only [h0, h1228, hlam]
                            · linarith only [h1228, h4, hlam]
                          · linarith only [h1, h1227, hlam]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [h1113, h1114, h1117, h1119, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1224_1]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [h1113, h1114, h1117, h1119, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1224_1]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [h0, hlam, p1224_0]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [hlam, p1224_0]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          rcases p1224_3 (m.d 0 1) (by simp) with h1236 | h1236
                          · rcases p1224_3 (m.d 0 2) (by simp) with h1237 | h1237
                            · rcases p1224_3 (m.d 0 3) (by simp) with h1238 | h1238
                              · linarith only [h1238, h4, hlam]
                              · rcases p1224_3 (m.d 0 4) (by simp) with h1240 | h1240
                                · linarith only [h1240, h5, hlam]
                                · linarith only [h1240, h7, hlam]
                            · linarith only [h1237, h4, hlam]
                          · linarith only [h1, h1236, hlam]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [h1113, h1114, h1117, h1119, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1224_1]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [h0, h1113, h1114, h1117, h1119, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1224_1]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [h1, hlam, p1224_1]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [h4, hlam, p1224_1]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [hlam, p1224_0]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [h7, hlam, p1224_1]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [h930, hlam, p1224_1]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [h2, hlam, p1224_0]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [h5, hlam, p1224_0]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [h1, h1114, h7, hc23, hc34, hlam, hphi, p1224_1]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [hlam, p1224_0]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [h1113, h1114, h1117, h1119, h7, hc23, hc34, hlam, hphi, p1224_1]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [h3, hlam, p1224_0]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [h6, hlam, p1224_1]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [h1, h1114, h930, hc23, hc35, hlam, hphi, p1224_1]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [h1113, hlam, p1224_1]
                        · have p1224_0 := h1224c.1
                          have p1224_1 := h1224c.2.1
                          have p1224_2 := h1224c.2.2.1
                          have p1224_3 := h1224c.2.2.2
                          linarith only [hlam, p1224_0]
                      · linarith only [h1, h1114, h1223, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h1115, h1116, h6, h930, hc24, hlam, hphi, ht45, u5elo3]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1264 | h1264
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1265 | h1265
            · linarith only [h1, h1265, h7, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1267 | h1267
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1268 | h1268
                · linarith only [h1114, h1115, h1268, h5, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1270 | h1270
                  · linarith only [h0, h1114, h1115, h1267, h1270, h3, h5, h930, hc01, hc45, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1272 | h1272
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1273 | h1273
                      · rcases h0bigk with h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c | h1274c
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [hlam, p1274_0]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [h1115, h5, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1274_1]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          rcases p1274_3 (m.d 0 1) (by simp) with h1277 | h1277
                          · rcases p1274_3 (m.d 0 2) (by simp) with h1278 | h1278
                            · linarith only [h0, h1278, hlam]
                            · linarith only [h1278, h4, hlam]
                          · linarith only [h1, h1277, hlam]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [h1115, h1264, h1270, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1274_1]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          rcases p1274_3 (m.d 0 1) (by simp) with h1283 | h1283
                          · rcases p1274_3 (m.d 0 2) (by simp) with h1284 | h1284
                            · linarith only [h0, h1284, hlam]
                            · linarith only [h1284, h6, hlam]
                          · linarith only [h1283, h3, hlam]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [h0, hlam, p1274_0]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [hlam, p1274_0]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          rcases p1274_3 (m.d 0 1) (by simp) with h1290 | h1290
                          · rcases p1274_3 (m.d 0 2) (by simp) with h1291 | h1291
                            · rcases p1274_3 (m.d 0 3) (by simp) with h1292 | h1292
                              · linarith only [h1292, h4, hlam]
                              · rcases p1274_3 (m.d 0 4) (by simp) with h1294 | h1294
                                · linarith only [h1294, h5, hlam]
                                · linarith only [h1294, h7, hlam]
                            · linarith only [h1291, h4, hlam]
                          · linarith only [h1, h1290, hlam]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [h1115, h1264, h1270, h5, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1274_1]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          rcases p1274_3 (m.d 0 1) (by simp) with h1300 | h1300
                          · rcases p1274_3 (m.d 0 2) (by simp) with h1301 | h1301
                            · rcases p1274_3 (m.d 0 3) (by simp) with h1302 | h1302
                              · linarith only [h1302, h4, hlam]
                              · rcases p1274_3 (m.d 0 4) (by simp) with h1304 | h1304
                                · linarith only [h1304, h5, hlam]
                                · linarith only [h1113, h1304, hlam]
                            · linarith only [h1301, h6, hlam]
                          · linarith only [h1300, h3, hlam]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [h1, hlam, p1274_1]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [h4, hlam, p1274_1]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [hlam, p1274_0]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [h7, hlam, p1274_1]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [h930, hlam, p1274_1]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [h2, hlam, p1274_0]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [h5, hlam, p1274_0]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [h1, h1114, h7, hc23, hc34, hlam, hphi, p1274_1]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [hlam, p1274_0]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [h1, h1114, h7, h930, hc23, hc34, hlam, hphi, p1274_1]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [h3, hlam, p1274_0]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [h6, hlam, p1274_1]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [h1, h1114, hc23, hlam, hphi, ht34, ht45, p1274_1, u5elo0]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [h1113, hlam, p1274_1]
                        · have p1274_0 := h1274c.1
                          have p1274_1 := h1274c.2.1
                          have p1274_2 := h1274c.2.2.1
                          have p1274_3 := h1274c.2.2.2
                          linarith only [hlam, p1274_0]
                      · linarith only [h1115, h1264, h1270, h1273, h2, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
                    · linarith only [h1115, h1264, h1267, h1270, h1272, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
              · linarith only [h1113, h1114, h1115, h1267, h7, hc23, hc34, hlam, hphi]
          · linarith only [h1114, h1264, hc23, hlam, hphi, ht34, ht45, u5elo2]
      · linarith only [h1114, h4, h930, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1329 | h1329
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1330 | h1330
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1331 | h1331
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1332 | h1332
            · linarith only [h1, h1113, h1332, h7, hc34, hlam, hphi, ht45, u5elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1334 | h1334
              · linarith only [h1113, h1334, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1336 | h1336
                · linarith only [h1, h1329, h1336, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1338 | h1338
                  · linarith only [h1, h1113, h1329, h1338, h7, h930, hc05, hlam, hphi, u5elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1340 | h1340
                    · linarith only [h0, h1113, h1330, h1340, h7, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1342 | h1342
                      · rcases h0bigk with h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c | h1343c
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          linarith only [hlam, p1343_0]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          linarith only [h4, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1343_1]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          rcases p1343_3 (m.d 0 1) (by simp) with h1346 | h1346
                          · rcases p1343_3 (m.d 0 2) (by simp) with h1347 | h1347
                            · linarith only [h0, h1347, hlam]
                            · linarith only [h1347, h4, hlam]
                          · linarith only [h1, h1346, hlam]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          rcases p1343_3 (m.d 0 1) (by simp) with h1351 | h1351
                          · rcases p1343_3 (m.d 0 2) (by simp) with h1352 | h1352
                            · linarith only [h0, h1352, hlam]
                            · linarith only [h1352, h5, hlam]
                          · linarith only [h1351, h2, hlam]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          rcases p1343_3 (m.d 0 1) (by simp) with h1356 | h1356
                          · rcases p1343_3 (m.d 0 2) (by simp) with h1357 | h1357
                            · linarith only [h0, h1357, hlam]
                            · linarith only [h1357, h6, hlam]
                          · linarith only [h1356, h3, hlam]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          linarith only [h0, hlam, p1343_0]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          linarith only [hlam, p1343_0]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          rcases p1343_3 (m.d 0 1) (by simp) with h1363 | h1363
                          · rcases p1343_3 (m.d 0 2) (by simp) with h1364 | h1364
                            · rcases p1343_3 (m.d 0 3) (by simp) with h1365 | h1365
                              · linarith only [h1365, h4, hlam]
                              · rcases p1343_3 (m.d 0 4) (by simp) with h1367 | h1367
                                · linarith only [h1367, h5, hlam]
                                · linarith only [h1367, h7, hlam]
                            · linarith only [h1364, h4, hlam]
                          · linarith only [h1, h1363, hlam]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          rcases p1343_3 (m.d 0 1) (by simp) with h1372 | h1372
                          · rcases p1343_3 (m.d 0 2) (by simp) with h1373 | h1373
                            · rcases p1343_3 (m.d 0 3) (by simp) with h1374 | h1374
                              · linarith only [h1374, h4, hlam]
                              · rcases p1343_3 (m.d 0 4) (by simp) with h1376 | h1376
                                · linarith only [h1376, h5, hlam]
                                · rcases p1343_3 (m.d 0 5) (by simp) with h1378 | h1378
                                  · linarith only [h1378, h6, hlam]
                                  · linarith only [h1113, h1378, hlam]
                            · linarith only [h1373, h5, hlam]
                          · linarith only [h1372, h2, hlam]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          rcases p1343_3 (m.d 0 1) (by simp) with h1383 | h1383
                          · rcases p1343_3 (m.d 0 2) (by simp) with h1384 | h1384
                            · rcases p1343_3 (m.d 0 3) (by simp) with h1385 | h1385
                              · linarith only [h1385, h4, hlam]
                              · rcases p1343_3 (m.d 0 4) (by simp) with h1387 | h1387
                                · linarith only [h1387, h5, hlam]
                                · rcases p1343_3 (m.d 0 5) (by simp) with h1389 | h1389
                                  · linarith only [h1389, h6, hlam]
                                  · rcases h2bigk with h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [hlam, p1391_0]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      rcases p1391_3 (m.d 0 2) (by simp) with h1393 | h1393
                                      · rcases p1391_3 (m.d 1 2) (by simp) with h1394 | h1394
                                        · linarith only [h0, h1394, hlam]
                                        · rcases p1391_3 (m.d 2 3) (by simp) with h1396 | h1396
                                          · linarith only [h1396, h4, hlam]
                                          · rcases p1391_3 (m.d 2 4) (by simp) with h1398 | h1398
                                            · linarith only [h1398, h5, hlam]
                                            · rcases p1391_3 (m.d 2 5) (by simp) with h1400 | h1400
                                              · linarith only [h1400, h6, hlam]
                                              · rcases h3bigk with h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c | h1402c
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [hlam, p1402_0]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [h1113, h1329, h7, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1343_1, p1402_1]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [h0, h1113, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1343_1, p1402_1]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [h7, hlam, p1402_0]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [h930, hlam, p1402_0]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [h1, hlam, p1402_0]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [hlam, p1402_0]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [h0, h1, h1113, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1343_1, p1402_1]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [h1332, hlam, p1402_0]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [h1, h1113, h1342, h7, hlam, p1402_1]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [h4, hlam, p1402_0]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [h1329, hlam, p1402_0]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [hlam, p1402_0]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [h1336, hlam, p1402_0]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [h1338, hlam, p1402_0]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  rcases p1402_3 (m.d 0 3) (by simp) with h1418 | h1418
                                                  · linarith only [h1418, hlam, p1402_0]
                                                  · rcases p1402_3 (m.d 1 3) (by simp) with h1420 | h1420
                                                    · linarith only [h1332, h1420, hlam]
                                                    · rcases p1402_3 (m.d 2 3) (by simp) with h1422 | h1422
                                                      · linarith only [h1336, h1422, hlam]
                                                      · rcases p1402_3 (m.d 3 4) (by simp) with h1424 | h1424
                                                        · rcases p1402_3 (m.d 3 5) (by simp) with h1425 | h1425
                                                          · linarith only [h1342, h1425, hlam]
                                                          · linarith only [h1425, h930, hlam]
                                                        · linarith only [h1424, hlam, p1402_0]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  rcases p1402_3 (m.d 0 3) (by simp) with h1429 | h1429
                                                  · linarith only [h1429, h7, hlam]
                                                  · linarith only [h1, h1429, hlam]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  rcases p1402_3 (m.d 0 3) (by simp) with h1432 | h1432
                                                  · linarith only [h1432, h7, hlam]
                                                  · linarith only [h1432, h4, hlam]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [hlam, p1402_0]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [h1113, h1342, h7, hc03, hc34, hlam, hphi, p1402_1]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [h1, hc13, hlam, hphi, ht34, ht45, p1402_1, u5elo3]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [h1329, hc23, hlam, hphi, ht34, ht45, p1402_1, u5elo3]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [hc23, hlam, hphi, ht34, ht45, p1402_1, u5elo3]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [h1342, hlam, p1402_0]
                                                · have p1402_0 := h1402c.1
                                                  have p1402_1 := h1402c.2.1
                                                  have p1402_2 := h1402c.2.2.1
                                                  have p1402_3 := h1402c.2.2.2
                                                  linarith only [hlam, p1402_0]
                                      · linarith only [h0, h1393, hlam]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [h1, h1113, h1329, h7, hlam, p1343_1, p1391_2]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [h1113, h5, hlam, p1343_1, p1391_2]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [h6, hlam, p1343_1, p1391_2]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [h0, hlam, p1391_0]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [hlam, p1391_0]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      rcases p1391_3 (m.d 0 2) (by simp) with h1448 | h1448
                                      · rcases p1391_3 (m.d 1 2) (by simp) with h1449 | h1449
                                        · rcases p1391_3 (m.d 2 3) (by simp) with h1450 | h1450
                                          · linarith only [h1450, hlam, p1391_0]
                                          · rcases p1391_3 (m.d 2 4) (by simp) with h1452 | h1452
                                            · linarith only [h1330, h1452, hlam]
                                            · linarith only [h1336, h1452, hlam]
                                        · linarith only [h1449, hlam, p1391_0]
                                      · linarith only [h1448, h4, hlam]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      rcases p1391_3 (m.d 0 2) (by simp) with h1457 | h1457
                                      · rcases p1391_3 (m.d 1 2) (by simp) with h1458 | h1458
                                        · rcases p1391_3 (m.d 2 3) (by simp) with h1459 | h1459
                                          · linarith only [h1329, h1459, hlam]
                                          · rcases p1391_3 (m.d 2 4) (by simp) with h1461 | h1461
                                            · linarith only [h1461, hlam, p1391_0]
                                            · rcases p1391_3 (m.d 2 5) (by simp) with h1463 | h1463
                                              · linarith only [h1331, h1463, hlam]
                                              · linarith only [h1340, h1463, hlam]
                                        · linarith only [h1458, hlam, p1391_0]
                                      · linarith only [h1457, h5, hlam]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      rcases p1391_3 (m.d 0 2) (by simp) with h1468 | h1468
                                      · rcases p1391_3 (m.d 1 2) (by simp) with h1469 | h1469
                                        · rcases p1391_3 (m.d 2 3) (by simp) with h1470 | h1470
                                          · linarith only [h1329, h1470, hlam]
                                          · rcases p1391_3 (m.d 2 4) (by simp) with h1472 | h1472
                                            · linarith only [h1330, h1472, hlam]
                                            · rcases p1391_3 (m.d 2 5) (by simp) with h1474 | h1474
                                              · linarith only [h1474, hlam, p1391_0]
                                              · rcases h3bigk with h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c | h1476c
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [hlam, p1476_0]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [h0, h1113, h1329, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1343_1, p1476_1]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [h0, h1113, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1343_1, p1476_1]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [h7, hlam, p1476_0]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [h930, hlam, p1476_0]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [h1, hlam, p1476_0]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [hlam, p1476_0]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [h0, h1, h1113, h7, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1343_1, p1476_1]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [h1332, hlam, p1476_0]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [h0, h1, h1113, h7, hc01, hc35, hlam, hphi, ht0b, ht5b, p1343_1, p1476_1]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [h4, hlam, p1476_0]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [h1329, hlam, p1476_0]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [hlam, p1476_0]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [h1336, hlam, p1476_0]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [h1338, hlam, p1476_0]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  rcases p1476_3 (m.d 0 3) (by simp) with h1492 | h1492
                                                  · linarith only [h1492, hlam, p1476_0]
                                                  · rcases p1476_3 (m.d 1 3) (by simp) with h1494 | h1494
                                                    · linarith only [h1332, h1494, hlam]
                                                    · rcases p1476_3 (m.d 2 3) (by simp) with h1496 | h1496
                                                      · linarith only [h1336, h1496, hlam]
                                                      · rcases p1476_3 (m.d 3 4) (by simp) with h1498 | h1498
                                                        · rcases p1476_3 (m.d 3 5) (by simp) with h1499 | h1499
                                                          · linarith only [h1342, h1499, hlam]
                                                          · linarith only [h1499, h930, hlam]
                                                        · linarith only [h1498, hlam, p1476_0]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  rcases p1476_3 (m.d 0 3) (by simp) with h1503 | h1503
                                                  · linarith only [h1503, h7, hlam]
                                                  · linarith only [h1, h1503, hlam]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  rcases p1476_3 (m.d 0 3) (by simp) with h1506 | h1506
                                                  · linarith only [h1506, h7, hlam]
                                                  · linarith only [h1506, h4, hlam]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [hlam, p1476_0]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [h1113, h1342, h7, hc03, hc34, hlam, hphi, p1476_1]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [h1, hc13, hlam, hphi, ht34, ht45, p1476_1, u5elo3]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [h1329, hc23, hlam, hphi, ht34, ht45, p1476_1, u5elo3]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [hc23, hlam, hphi, ht34, ht45, p1476_1, u5elo3]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [h1342, hlam, p1476_0]
                                                · have p1476_0 := h1476c.1
                                                  have p1476_1 := h1476c.2.1
                                                  have p1476_2 := h1476c.2.2.1
                                                  have p1476_3 := h1476c.2.2.2
                                                  linarith only [hlam, p1476_0]
                                        · linarith only [h1469, hlam, p1391_0]
                                      · linarith only [h1468, h6, hlam]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [h4, hlam, p1391_0]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [h1329, hlam, p1391_0]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [hlam, p1391_0]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [h1336, hlam, p1391_0]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [h1338, hlam, p1391_0]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [h5, hlam, p1391_0]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [h1330, hlam, p1391_0]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [h0, h1113, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1343_1, p1391_1]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [hlam, p1391_0]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [h1340, hlam, p1391_1]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [h6, hlam, p1391_0]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [h1331, hlam, p1391_0]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [h0, h1331, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1343_1, p1391_1]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [h0, h1331, h3, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1343_1, p1391_1]
                                    · have p1391_0 := h1391c.1
                                      have p1391_1 := h1391c.2.1
                                      have p1391_2 := h1391c.2.2.1
                                      have p1391_3 := h1391c.2.2.2
                                      linarith only [hlam, p1391_0]
                            · linarith only [h1384, h6, hlam]
                          · linarith only [h1383, h3, hlam]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          linarith only [h1, hlam, p1343_1]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          linarith only [h4, hlam, p1343_1]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          linarith only [hlam, p1343_0]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          linarith only [h7, hlam, p1343_1]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          linarith only [h930, hlam, p1343_1]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          linarith only [h2, hlam, p1343_0]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          linarith only [h5, hlam, p1343_0]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          linarith only [h1, h1113, hc13, hc45, hlam, hphi, ht34, p1343_1]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          linarith only [hlam, p1343_0]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          linarith only [h1113, hlam, p1343_0]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          linarith only [h3, hlam, p1343_0]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          linarith only [h6, hlam, p1343_1]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          linarith only [h1, h930, hc13, hlam, hphi, ht34, ht45, p1343_1, u5elo3]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          linarith only [h930, hc04, hlam, hphi, ht45, p1343_1, u5elo3]
                        · have p1343_0 := h1343c.1
                          have p1343_1 := h1343c.2.1
                          have p1343_2 := h1343c.2.2.1
                          have p1343_3 := h1343c.2.2.2
                          linarith only [hlam, p1343_0]
                      · linarith only [h1, h1329, h1342, h7, hc23, hlam, hphi, ht34, ht45, u5elo4]
          · linarith only [h1329, h1331, h6, h930, hc23, hlam, hphi, ht34, ht45, u5elo3]
        · linarith only [h1113, h1329, h1330, h5, hc23, hlam, hphi, ht34, ht45, u5elo4]
      · linarith only [h1113, h1329, h4, h7, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]

set_option maxHeartbeats 5040000 in
set_option maxHeartbeats 5040000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6 h7

set_option maxHeartbeats 5040000 in
set_option maxHeartbeats 5040000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  linarith only [h4, h6, hc23, hlam, hphi, ht34, ht45, u5elo2]

set_option maxHeartbeats 5040000 in
set_option maxHeartbeats 5040000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5 h6

set_option maxHeartbeats 5040000 in
set_option maxHeartbeats 5040000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h1555 | h1555
  · rcases m.htr 0 3 4 (by decide) (by decide) with h1556 | h1556
    · linarith only [h1556, h4, h5, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h1558 | h1558
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1559 | h1559
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1560 | h1560
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1561 | h1561
            · linarith only [h0, h1561, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1563 | h1563
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1564 | h1564
                · linarith only [h1, h1556, h1558, h1564, hc01, hc35, hlam, hphi, ht0b, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1566 | h1566
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1567 | h1567
                    · linarith only [h0, h1556, h1558, h1560, h1567, hc02, hc35, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1569 | h1569
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1570 | h1570
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1571 | h1571
                          · rcases h0bigk with h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c | h1572c
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [hlam, p1572_0]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1569, h1571, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p1572_1]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1, h1560, h1569, h1571, hc01, hc45, hlam, hphi, ht0b, ht5b, p1572_1]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1569, h1571, h4, h5, hc01, hc45, hlam, hphi, ht0b, ht5b, p1572_1]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              rcases p1572_3 (m.d 0 1) (by simp) with h1577 | h1577
                              · rcases p1572_3 (m.d 0 2) (by simp) with h1578 | h1578
                                · linarith only [h0, h1578, hlam]
                                · linarith only [h1555, h1578, hlam]
                              · linarith only [h1577, h3, hlam]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h0, hlam, p1572_0]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [hlam, p1572_0]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1, h1560, h1569, h1571, hc02, hc45, hlam, hphi, ht0b, ht5b, p1572_1]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h5, hlam, p1572_1]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1567, h5, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1572_1]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1, hlam, p1572_1]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h4, hlam, p1572_1]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [hlam, p1572_0]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1556, hlam, p1572_1]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1563, h1567, h3, h4, h5, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1572_1]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h2, hlam, p1572_0]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h0, h1560, h1569, h1571, hc04, hc45, hlam, hphi, ht0b, ht5b, p1572_1]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1567, h5, hc03, hc34, hlam, hphi, p1572_1]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [hlam, p1572_0]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              rcases p1572_3 (m.d 0 1) (by simp) with h1596 | h1596
                              · rcases p1572_3 (m.d 0 2) (by simp) with h1597 | h1597
                                · linarith only [h1597, h5, hlam]
                                · linarith only [h1555, h1597, hlam]
                              · linarith only [h1596, h3, hlam]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h3, hlam, p1572_0]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1555, hlam, p1572_1]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1558, hlam, p1572_0]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [h1559, hlam, p1572_1]
                            · have p1572_0 := h1572c.1
                              have p1572_1 := h1572c.2.1
                              have p1572_2 := h1572c.2.2.1
                              have p1572_3 := h1572c.2.2.2
                              linarith only [hlam, p1572_0]
                          · linarith only [h1560, h1561, h1567, h1569, h1571, h2, h5, hc35, hlam, hphi, u5elo4]
                        · linarith only [h0, h1560, h1566, h1569, h1570, h2, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h1558, h1567, h1569, h4, h5, hc23, hc34, hlam, hphi]
                  · linarith only [h1559, h1560, h1561, h1566, hc23, hlam, hphi, ht34, ht45, u5elo0]
              · linarith only [h1560, h1563, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h1560, h4, h5, hc12, hc24, hlam, hphi]
        · linarith only [h1559, h4, h5, hc23, hlam, hphi, ht34, ht45, u5elo4]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h1613 | h1613
        · rcases m.htr 1 2 3 (by decide) (by decide) with h1614 | h1614
          · rcases m.htr 1 2 4 (by decide) (by decide) with h1615 | h1615
            · linarith only [h0, h1615, h5, hlam]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h1617 | h1617
              · rcases m.htr 1 3 4 (by decide) (by decide) with h1618 | h1618
                · linarith only [h1, h1558, h1618, hc34, hlam, hphi, ht45, u5elo3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h1620 | h1620
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1621 | h1621
                    · linarith only [h0, h1, h1556, h1614, h1621, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h1623 | h1623
                      · linarith only [h1, h1558, h1614, h1623, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h1625 | h1625
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h1626 | h1626
                          · rcases h0bigk with h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c | h1627c
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [hlam, p1627_0]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [h0, h1617, hc01, hc25, hlam, hphi, ht0b, ht5b, p1627_1]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              rcases p1627_3 (m.d 0 1) (by simp) with h1630 | h1630
                              · rcases p1627_3 (m.d 0 2) (by simp) with h1631 | h1631
                                · linarith only [h0, h1631, hlam]
                                · linarith only [h1631, h4, hlam]
                              · linarith only [h1, h1630, hlam]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [h0, h1617, h1623, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1627_1]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              rcases p1627_3 (m.d 0 1) (by simp) with h1636 | h1636
                              · rcases p1627_3 (m.d 0 2) (by simp) with h1637 | h1637
                                · linarith only [h0, h1637, hlam]
                                · linarith only [h1555, h1637, hlam]
                              · linarith only [h1636, h3, hlam]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [h0, hlam, p1627_0]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [hlam, p1627_0]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [h1, h1614, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1627_1]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [h5, hlam, p1627_1]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [h1621, h5, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1627_1]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [h1, hlam, p1627_1]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [h4, hlam, p1627_1]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [hlam, p1627_0]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [h1556, hlam, p1627_1]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [h1558, hlam, p1627_1]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [h2, hlam, p1627_0]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [h0, h1617, h1623, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1627_1]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [h1, h1614, h1621, h5, hc23, hc34, hlam, hphi, p1627_1]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [hlam, p1627_0]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [h1, h1558, h1614, h1621, h5, hc23, hc34, hlam, hphi, p1627_1]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [h3, hlam, p1627_0]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [h1555, hlam, p1627_1]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [h1, h1614, hc23, hlam, hphi, ht34, ht45, p1627_1, u5elo0]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [h1613, hlam, p1627_1]
                            · have p1627_0 := h1627c.1
                              have p1627_1 := h1627c.2.1
                              have p1627_2 := h1627c.2.2.1
                              have p1627_3 := h1627c.2.2.2
                              linarith only [hlam, p1627_0]
                          · linarith only [h0, h1617, h1621, h1625, h1626, h5, hlam]
                        · linarith only [h1625, h5, hc02, hlam, hphi, ht23, ht34, ht45, u5elo4]
                  · linarith only [h1614, h1615, h1620, hc23, hlam, hphi, ht34, ht45, u5elo4]
              · linarith only [h1614, h1617, hc23, hlam, hphi, ht34, ht45, u5elo2]
          · linarith only [h1558, h1614, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
        · linarith only [h1613, h4, h5, hc23, hlam, hphi, ht34, ht45, u5elo4]
  · linarith only [h1555, h4, hc23, hlam, hphi, ht34, ht45, u5elo2]

set_option maxHeartbeats 5040000 in
set_option maxHeartbeats 5040000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_0_s3_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 h4 h5

end R2N4
