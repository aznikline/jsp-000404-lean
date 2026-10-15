import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_51S1

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5216000 in
theorem r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h1 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h912 | h912
  · rcases m.htr 0 4 5 (by decide) (by decide) with h913 | h913
    · rcases m.htr 1 2 3 (by decide) (by decide) with h914 | h914
      · rcases m.htr 1 2 5 (by decide) (by decide) with h915 | h915
        · linarith only [h1, h915, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h917 | h917
          · rcases m.htr 1 3 5 (by decide) (by decide) with h918 | h918
            · linarith only [h914, h915, h918, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h920 | h920
              · linarith only [h914, h915, h917, h920, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h922 | h922
                · linarith only [h914, h915, h922, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h1, h912, h917, h918, h922, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h925 | h925
            · linarith only [h914, h915, h925, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h927 | h927
              · rcases m.htr 2 3 4 (by decide) (by decide) with h928 | h928
                · linarith only [h914, h917, h928, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo1]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h930 | h930
                  · linarith only [h914, h915, h925, h930, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                  · linarith only [h1, h912, h930, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h933 | h933
                · linarith only [h914, h917, h933, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h935 | h935
                  · linarith only [h914, h915, h935, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                  · linarith only [h1, h912, h935, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h938 | h938
        · linarith only [h1, h914, h938, hc02, hlam, hphi, u2elo2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h940 | h940
          · rcases m.htr 1 3 5 (by decide) (by decide) with h941 | h941
            · rcases m.htr 1 4 5 (by decide) (by decide) with h942 | h942
              · rcases m.htr 2 3 4 (by decide) (by decide) with h943 | h943
                · rcases m.htr 2 3 5 (by decide) (by decide) with h944 | h944
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h945 | h945
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h946 | h946
                      · rcases h5bigk with h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c | h947c
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [hlam, p947_0]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h1, h938, h945, hc12, hlam, hphi, p947_1, u2elo3]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h1, hlam, p947_0]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h1, h945, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p947_1, u2elo3]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h1, h945, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p947_1, u2elo3]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h0, hlam, p947_0]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [hlam, p947_0]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h938, hlam, p947_0]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht0b, ht5b, p947_1]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h0, h1, h945, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p947_1, u2elo3]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h945, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p947_1, u2elo3]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h945, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p947_1, u2elo3]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [hlam, p947_0]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h943, h945, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p947_1, u2elo2]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h943, h945, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p947_1, u2elo2]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h912, hlam, p947_1]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h941, hlam, p947_1]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h944, hlam, p947_0]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [hlam, p947_0]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h912, hc03, hc45, hlam, hphi, ht0b, ht5b, p947_1]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h913, hlam, p947_1]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h942, hlam, p947_1]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h945, hlam, p947_1]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [h946, hlam, p947_1]
                        · have p947_0 := h947c.1
                          have p947_1 := h947c.2.1
                          have p947_2 := h947c.2.2.1
                          have p947_3 := h947c.2.2.2
                          linarith only [hlam, p947_0]
                      · rcases h5bigk with h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [hlam, p973_0]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h1, h943, h945, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p973_1, u2elo2]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h1, hlam, p973_0]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h1, h943, h945, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p973_1, u2elo2]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h1, h943, h945, h946, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p973_1, u2elo2]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h0, hlam, p973_0]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [hlam, p973_0]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h938, hlam, p973_0]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht0b, ht5b, p973_1]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h0, h1, h943, h945, h946, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p973_1, u2elo2]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h943, h945, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p973_1, u2elo2]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h943, h945, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p973_1, u2elo2]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [hlam, p973_0]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h943, h945, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p973_1, u2elo2]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h943, h945, h946, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p973_1, u2elo2]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h912, hlam, p973_1]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h941, hlam, p973_1]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h944, hlam, p973_0]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [hlam, p973_0]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h946, hlam, p973_0]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h913, hlam, p973_1]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h942, hlam, p973_1]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h945, hlam, p973_1]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [h913, hc04, hc35, hlam, hphi, ht0b, ht5b, p973_1]
                        · have p973_0 := h973c.1
                          have p973_1 := h973c.2.1
                          have p973_2 := h973c.2.2.1
                          have p973_3 := h973c.2.2.2
                          linarith only [hlam, p973_0]
                    · linarith only [h0, h1, h942, h945, hlam]
                  · linarith only [h1, h912, h914, h944, hc12, hlam, hphi, u2elo4]
                · linarith only [h914, h940, h943, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1002 | h1002
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1003 | h1003
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1004 | h1004
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1005 | h1005
                      · linarith only [h1005, h940, h942, hlam]
                      · rcases h5bigk with h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c | h1007c
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [hlam, p1007_0]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h1, h1002, h1004, h938, hc12, hlam, hphi, p1007_1, u2elo2]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h1, hlam, p1007_0]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h1, h1002, h1004, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1007_1, u2elo2]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h1, h1002, h1004, h942, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1007_1, u2elo2]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h0, hlam, p1007_0]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [hlam, p1007_0]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h938, hlam, p1007_0]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht0b, ht5b, p1007_1]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h942, hlam, p1007_0]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h1002, h1004, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1007_1, u2elo2]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h1002, h1004, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1007_1, u2elo2]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [hlam, p1007_0]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h1002, h1004, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1007_1, u2elo2]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h1002, h1004, h940, h942, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1007_1, u2elo2]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h912, hlam, p1007_1]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h941, hlam, p1007_1]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h1003, hlam, p1007_0]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [hlam, p1007_0]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h1005, hlam, p1007_0]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h913, hlam, p1007_1]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h938, hc12, hc45, hlam, hphi, ht23, ht34, p1007_1]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h1004, hlam, p1007_1]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [h1002, h1004, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1007_1, u2elo2]
                        · have p1007_0 := h1007c.1
                          have p1007_1 := h1007c.2.1
                          have p1007_2 := h1007c.2.2.1
                          have p1007_3 := h1007c.2.2.2
                          linarith only [hlam, p1007_0]
                    · linarith only [h1, h1004, h913, hlam]
                  · linarith only [h1, h1003, h912, h914, hc12, hlam, hphi, u2elo4]
                · linarith only [h1002, h914, h940, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1036 | h1036
              · linarith only [h1036, h940, h941, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1038 | h1038
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1039 | h1039
                  · linarith only [h1039, h940, h941, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h1, h1039, h912, h914, hc12, hlam, hphi, u2elo4]
                · linarith only [h0, h1038, h914, h940, h941, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1043 | h1043
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1044 | h1044
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1045 | h1045
                · linarith only [h1043, h1045, h940, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1047 | h1047
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1048 | h1048
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1049 | h1049
                      · rcases h5bigk with h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c | h1050c
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [hlam, p1050_0]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1, h1045, h1047, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1, hlam, p1050_0]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1, h1045, h1047, h1049, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1, h1045, h1047, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h0, hlam, p1050_0]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [hlam, p1050_0]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h938, hlam, p1050_0]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h0, h1049, hc01, hc45, hlam, hphi, ht0b, ht5b, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1045, h1047, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1045, h1047, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [hlam, p1050_0]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1045, h1047, h1049, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1045, h1047, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h912, hlam, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1043, hlam, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1047, hlam, p1050_0]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [hlam, p1050_0]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1043, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h913, hlam, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1044, hlam, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1048, hlam, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [h1049, hlam, p1050_1]
                        · have p1050_0 := h1050c.1
                          have p1050_1 := h1050c.2.1
                          have p1050_2 := h1050c.2.2.1
                          have p1050_3 := h1050c.2.2.2
                          linarith only [hlam, p1050_0]
                      · linarith only [h1, h1045, h1047, h1049, hc02, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h0, h1, h1044, h1045, h1047, h1048, hlam]
                  · linarith only [h1043, h1047, h914, hlam]
              · linarith only [h1043, h1044, h940, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1080 | h1080
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1081 | h1081
                · linarith only [h1081, h914, h940, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1083 | h1083
                  · linarith only [h1043, h1081, h1083, h914, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h1083, h912, h914, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1086 | h1086
                · linarith only [h1086, h914, h940, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1088 | h1088
                  · linarith only [h1043, h1086, h1088, h914, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h1088, h912, h914, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1091 | h1091
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1092 | h1092
        · linarith only [h1, h1092, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1094 | h1094
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1095 | h1095
            · linarith only [h1091, h1092, h1095, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1097 | h1097
              · linarith only [h1094, h1095, h1097, h912, h913, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1099 | h1099
                · linarith only [h1091, h1092, h1099, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h1094, h1095, h1099, hc23, hc35, hlam, hphi]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1102 | h1102
            · linarith only [h1091, h1092, h1102, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1104 | h1104
              · linarith only [h0, h1104, h913, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1106 | h1106
                · linarith only [h1091, h1092, h1106, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1108 | h1108
                  · linarith only [h1091, h1092, h1102, h1108, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · linarith only [h1, h1108, h912, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1111 | h1111
        · linarith only [h1, h1091, h1111, hc02, hlam, hphi, u2elo2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1113 | h1113
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1114 | h1114
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1115 | h1115
              · linarith only [h0, h1115, h913, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1117 | h1117
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1118 | h1118
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1119 | h1119
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1120 | h1120
                      · linarith only [h1113, h1115, h1120, hlam]
                      · rcases h5bigk with h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [hlam, p1122_0]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [h1117, h1119, h913, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1122_1, u2elo2]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [h1, hlam, p1122_0]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [h1117, h1119, h913, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1122_1, u2elo2]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [h913, hlam, p1122_0]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [h0, hlam, p1122_0]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [hlam, p1122_0]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [h1111, hlam, p1122_0]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [h0, hc01, hc35, hlam, hphi, ht0b, ht5b, p1122_1]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [h1115, hlam, p1122_0]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1122_1, u2elo4]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1122_1, u2elo4]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [hlam, p1122_0]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [h1118, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1122_1, u2elo2]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [h1115, h1117, h1119, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1122_1, u2elo2]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [h912, hlam, p1122_1]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [h1114, hlam, p1122_1]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [h1118, hlam, p1122_0]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [hlam, p1122_0]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [h1120, hlam, p1122_0]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [h0, h1111, hc12, hc45, hlam, hphi, ht23, ht34, p1122_1]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [h1111, hc12, hc45, hlam, hphi, ht23, ht34, p1122_1]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [h1119, hlam, p1122_1]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [h1117, h1119, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p1122_1, u2elo2]
                        · have p1122_0 := h1122c.1
                          have p1122_1 := h1122c.2.1
                          have p1122_2 := h1122c.2.2.1
                          have p1122_3 := h1122c.2.2.2
                          linarith only [hlam, p1122_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1148 | h1148
                      · linarith only [h1, h1091, h1113, h1119, h1148, hc02, hlam, hphi, u2elo2]
                      · rcases h5bigk with h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c | h1150c
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1, h1111, hc12, hlam, hphi, p1150_1, u2elo4]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1, hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1, h1148, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1150_1, u2elo4]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h913, hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h0, hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1111, hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h0, h1148, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p1150_1]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1115, hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1150_1, u2elo4]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1115, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1150_1, u2elo4]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1118, h1148, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1150_1, u2elo2]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1119, hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h912, hlam, p1150_1]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1114, hlam, p1150_1]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1118, hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1148, hlam, p1150_0]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h0, h1111, hc12, hc45, hlam, hphi, ht23, ht34, p1150_1]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1111, hc12, hc45, hlam, hphi, ht23, ht34, p1150_1]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1, hc02, hc45, hlam, hphi, ht23, ht34, p1150_1]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [h1148, hc34, hc45, hlam, hphi, p1150_1]
                        · have p1150_0 := h1150c.1
                          have p1150_1 := h1150c.2.1
                          have p1150_2 := h1150c.2.2.1
                          have p1150_3 := h1150c.2.2.2
                          linarith only [hlam, p1150_0]
                  · linarith only [h1, h1091, h1118, h912, hc12, hlam, hphi, u2elo4]
                · linarith only [h1091, h1113, h1117, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1178 | h1178
              · linarith only [h1, h1113, h1114, h1178, h912, h913, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1180 | h1180
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1181 | h1181
                  · linarith only [h1113, h1114, h1181, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · linarith only [h1, h1091, h1181, h912, hc12, hlam, hphi, u2elo4]
                · linarith only [h0, h1091, h1113, h1114, h1180, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1185 | h1185
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1186 | h1186
              · linarith only [h0, h1186, h913, hlam]
              · linarith only [h1113, h1185, h1186, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1189 | h1189
              · linarith only [h1185, h1189, h912, h913, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1191 | h1191
                · linarith only [h1091, h1113, h1191, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1193 | h1193
                  · linarith only [h1091, h1185, h1191, h1193, hc12, hlam, hphi, u2elo3]
                  · linarith only [h1, h1091, h1193, h912, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h1196 | h1196
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1197 | h1197
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1198 | h1198
        · linarith only [h1, h1198, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1200 | h1200
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1201 | h1201
            · linarith only [h1197, h1198, h1201, h912, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1203 | h1203
              · linarith only [h1197, h1198, h1200, h1203, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1205 | h1205
                · linarith only [h1197, h1198, h1205, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h1197, h1198, h1200, h1205, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1208 | h1208
            · linarith only [h0, h1197, h1198, h1208, h912, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1210 | h1210
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1211 | h1211
                · linarith only [h1197, h1198, h1200, h1211, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1213 | h1213
                  · linarith only [h1197, h1198, h1208, h1213, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1215 | h1215
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1216 | h1216
                      · rcases h5bigk with h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c | h1217c
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [hlam, p1217_0]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [h1, h1198, h1215, hc12, hlam, hphi, p1217_1, u2elo3]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [h1, hlam, p1217_0]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [h912, hlam, p1217_0]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [h1, h1215, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1217_1, u2elo3]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [h0, hlam, p1217_0]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [hlam, p1217_0]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [h1198, hlam, p1217_0]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [h1208, hlam, p1217_0]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p1217_1]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [h1215, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1217_1, u2elo3]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [h1215, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1217_1, u2elo3]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [hlam, p1217_0]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [h1213, hlam, p1217_1]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [h1215, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1217_1, u2elo3]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [h0, h1197, h1198, hc23, hc35, hlam, hphi, p1217_1]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [h1197, h1198, hc23, hc35, hlam, hphi, p1217_1]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [h1, hc02, hc35, hlam, hphi, ht23, p1217_1]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [hlam, p1217_0]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          rcases p1217_3 (m.d 0 5) (by simp) with h1237 | h1237
                          · linarith only [h1237, h912, hlam]
                          · linarith only [h1196, h1237, hlam]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [h1196, hlam, p1217_1]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [h1210, hlam, p1217_1]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [h1215, hlam, p1217_1]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [h1216, hlam, p1217_1]
                        · have p1217_0 := h1217c.1
                          have p1217_1 := h1217c.2.1
                          have p1217_2 := h1217c.2.2.1
                          have p1217_3 := h1217c.2.2.2
                          linarith only [hlam, p1217_0]
                      · linarith only [h1200, h1210, h1216, hlam]
                    · linarith only [h0, h1, h1210, h1215, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1247 | h1247
                · linarith only [h1197, h1198, h1247, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1249 | h1249
                  · linarith only [h1197, h1198, h1249, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1251 | h1251
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1252 | h1252
                      · rcases h5bigk with h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c | h1253c
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [hlam, p1253_0]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h1, h1197, h1198, h1251, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1253_1, u2elo3]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h1, hlam, p1253_0]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h912, hlam, p1253_0]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h1, h1251, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1253_1, u2elo3]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h0, hlam, p1253_0]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [hlam, p1253_0]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h1198, hlam, p1253_0]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h1208, hlam, p1253_0]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h1210, hlam, p1253_0]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h1251, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1253_1, u2elo3]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h1197, h1198, h1251, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1253_1, u2elo3]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [hlam, p1253_0]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h1249, hlam, p1253_1]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h1197, h1200, h1210, h1251, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1253_1, u2elo3]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h1196, h1197, h1200, h1210, hc23, hc35, hlam, hphi, p1253_1]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h1197, h1198, hc23, hc35, hlam, hphi, p1253_1]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h1, hc02, hc35, hlam, hphi, ht23, p1253_1]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [hlam, p1253_0]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h1197, h1200, h1210, h1252, hc23, hc34, hlam, hphi, p1253_1]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h1196, hlam, p1253_1]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h1197, h1198, h1251, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1253_1, u2elo3]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h1251, hlam, p1253_1]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [h1252, hlam, p1253_1]
                        · have p1253_0 := h1253c.1
                          have p1253_1 := h1253c.2.1
                          have p1253_2 := h1253c.2.2.1
                          have p1253_3 := h1253c.2.2.2
                          linarith only [hlam, p1253_0]
                      · linarith only [h1197, h1200, h1251, h1252, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · linarith only [h1, h1196, h1251, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1281 | h1281
        · linarith only [h1, h1197, h1281, hc02, hlam, hphi, u2elo2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1283 | h1283
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1284 | h1284
            · linarith only [h0, h1284, h912, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1286 | h1286
              · linarith only [h1283, h1284, h1286, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1288 | h1288
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1289 | h1289
                  · linarith only [h1197, h1284, h1289, hc12, hlam, hphi, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1291 | h1291
                    · linarith only [h1288, h1289, h1291, hlam]
                    · linarith only [h1, h1196, h1291, hlam]
                · linarith only [h1197, h1283, h1288, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1295 | h1295
            · linarith only [h1283, h1295, h912, hc03, hc34, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1297 | h1297
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1298 | h1298
                · linarith only [h1197, h1283, h1298, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1300 | h1300
                  · linarith only [h1298, h1300, h912, hc03, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1302 | h1302
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1303 | h1303
                      · rcases h5bigk with h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c | h1304c
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [hlam, p1304_0]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [h1, h1297, h1302, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1304_1, u2elo3]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [h1, hlam, p1304_0]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [h912, hlam, p1304_0]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [h1, h1302, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1304_1, u2elo3]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [h0, hlam, p1304_0]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [hlam, p1304_0]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [h1281, hlam, p1304_0]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [h1295, hlam, p1304_0]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [h0, hc01, hc45, hlam, hphi, ht0b, ht5b, p1304_1]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [h1302, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1304_1, u2elo3]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [h1302, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1304_1, u2elo3]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [hlam, p1304_0]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [h1300, hlam, p1304_1]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [h1302, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1304_1, u2elo3]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [h0, h1197, h1295, h1303, hc12, hc34, hlam, hphi, ht23, p1304_1]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [h1197, h1295, h1303, hc12, hc34, hlam, hphi, ht23, p1304_1]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [h1300, h1303, hc23, hc34, hlam, hphi, p1304_1]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [hlam, p1304_0]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          rcases p1304_3 (m.d 0 5) (by simp) with h1324 | h1324
                          · linarith only [h1324, h912, hlam]
                          · linarith only [h1196, h1324, hlam]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [h1196, hlam, p1304_1]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [h1297, hlam, p1304_1]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [h1302, hlam, p1304_1]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [h1303, hlam, p1304_1]
                        · have p1304_0 := h1304c.1
                          have p1304_1 := h1304c.2.1
                          have p1304_2 := h1304c.2.2.1
                          have p1304_3 := h1304c.2.2.2
                          linarith only [hlam, p1304_0]
                      · linarith only [h1, h1196, h1197, h1283, h1303, hc12, hlam, hphi, u2elo4]
                    · linarith only [h0, h1, h1197, h1297, h1298, h1302, hc12, hlam, hphi, u2elo4]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1334 | h1334
                · linarith only [h1197, h1283, h1334, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1336 | h1336
                  · linarith only [h1334, h1336, h912, hc03, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1338 | h1338
                    · linarith only [h1197, h1283, h1297, h1338, hc12, hlam, hphi, u2elo3]
                    · linarith only [h1, h1196, h1197, h1334, h1338, hc12, hlam, hphi, u2elo4]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1341 | h1341
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1342 | h1342
        · linarith only [h1, h1342, hc02, hlam, hphi, u2elo1]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1344 | h1344
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1345 | h1345
            · linarith only [h1, h1341, h1342, h1345, h912, hc02, hlam, hphi, u2elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1347 | h1347
              · linarith only [h0, h1196, h1341, h1342, h1344, h1347, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1349 | h1349
                · linarith only [h1341, h1342, h1349, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · linarith only [h1341, h1342, h1344, h1349, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1352 | h1352
            · linarith only [h1341, h1342, h1352, h912, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1354 | h1354
              · linarith only [h0, h1196, h1354, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1356 | h1356
                · linarith only [h1341, h1342, h1344, h1356, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1358 | h1358
                  · linarith only [h0, h1341, h1342, h1358, h912, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1360 | h1360
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1361 | h1361
                      · rcases h5bigk with h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c | h1362c
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [hlam, p1362_0]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h1196, h1342, h1360, hc12, hlam, hphi, p1362_1, u2elo3]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h1, hlam, p1362_0]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h912, hlam, p1362_0]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h1196, hlam, p1362_0]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h0, hlam, p1362_0]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [hlam, p1362_0]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h1342, hlam, p1362_0]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h1352, hlam, p1362_0]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h1354, hlam, p1362_0]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h1360, hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1362_1, u2elo3]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h1341, h1342, h1360, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1362_1, u2elo3]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [hlam, p1362_0]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h1358, hlam, p1362_1]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h1354, h1360, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1362_1, u2elo3]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h0, h1341, h1342, hc23, hc35, hlam, hphi, p1362_1]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h1341, h1342, hc23, hc35, hlam, hphi, p1362_1]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h1, hc02, hc35, hlam, hphi, ht23, p1362_1]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [hlam, p1362_0]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h0, h1196, h1341, h1342, h1361, hc23, hc34, hlam, hphi, p1362_1]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h0, h1341, h1342, h1360, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1362_1, u2elo3]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h1341, h1342, h1360, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1362_1, u2elo3]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h1360, hlam, p1362_1]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [h1361, hlam, p1362_1]
                        · have p1362_0 := h1362c.1
                          have p1362_1 := h1362c.2.1
                          have p1362_2 := h1362c.2.2.1
                          have p1362_3 := h1362c.2.2.2
                          linarith only [hlam, p1362_0]
                      · linarith only [h1341, h1344, h1360, h1361, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1389 | h1389
                      · linarith only [h1341, h1342, h1360, h1389, hc23, hc34, hlam, hphi]
                      · rcases h5bigk with h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c | h1391c
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [hlam, p1391_0]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [h1341, h1342, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1391_1]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [h1, hlam, p1391_0]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [h912, hlam, p1391_0]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [h1196, hlam, p1391_0]
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
                          linarith only [h1342, hlam, p1391_0]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [h1352, hlam, p1391_0]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [h1354, hlam, p1391_0]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1391_1, u2elo4]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [h1342, hc12, hlam, hphi, p1391_1, u2elo4]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [hlam, p1391_0]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [h1358, hlam, p1391_1]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [h1360, hlam, p1391_0]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [h0, h1341, h1342, hc23, hc35, hlam, hphi, p1391_1]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [h1341, h1342, h1389, hc23, hc45, hlam, hphi, ht34, p1391_1]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [h1, h1389, hc02, hc45, hlam, hphi, ht23, ht34, p1391_1]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [hlam, p1391_0]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [h1389, hlam, p1391_0]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [h0, h1341, h1342, hc23, hc45, hlam, hphi, ht34, p1391_1]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [h1341, h1342, hc23, hc45, hlam, hphi, ht34, p1391_1]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [h1341, h1342, hc23, hc45, hlam, hphi, ht34, p1391_1]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [h912, hc03, hc45, hlam, hphi, ht34, p1391_1]
                        · have p1391_0 := h1391c.1
                          have p1391_1 := h1391c.2.1
                          have p1391_2 := h1391c.2.2.1
                          have p1391_3 := h1391c.2.2.2
                          linarith only [hlam, p1391_0]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1417 | h1417
        · linarith only [h1, h1341, h1417, hc02, hlam, hphi, u2elo2]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1419 | h1419
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1420 | h1420
            · linarith only [h0, h1420, h912, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1422 | h1422
              · linarith only [h0, h1196, h1419, h1420, h1422, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1424 | h1424
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1425 | h1425
                  · linarith only [h1419, h1420, h1425, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1427 | h1427
                    · linarith only [h1424, h1425, h1427, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1429 | h1429
                      · linarith only [h1341, h1419, h1425, h1427, h1429, hlam]
                      · rcases h5bigk with h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c | h1431c
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [hlam, p1431_0]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [h1, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1431_1, u2elo4]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [h1, hlam, p1431_0]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [h912, hlam, p1431_0]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [h1196, hlam, p1431_0]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [h0, hlam, p1431_0]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [hlam, p1431_0]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [h1417, hlam, p1431_0]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [h1420, hlam, p1431_0]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [h1422, hlam, p1431_0]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p1431_1, u2elo4]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p1431_1, u2elo4]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [hlam, p1431_0]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [h1425, hlam, p1431_1]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [h1427, hlam, p1431_0]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [h1, hc02, hc35, hlam, hphi, ht23, p1431_1]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [h1417, h1429, hc12, hc45, hlam, hphi, ht23, ht34, p1431_1]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [h1, h1429, hc02, hc45, hlam, hphi, ht23, ht34, p1431_1]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [hlam, p1431_0]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [h1429, hlam, p1431_0]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [h0, h1419, h1420, hc34, hc45, hlam, hphi, p1431_1]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [h1419, h1420, hc34, hc45, hlam, hphi, p1431_1]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [h0, h1, h1419, h1420, hc34, hc45, hlam, hphi, p1431_1]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [h912, hc03, hc45, hlam, hphi, ht34, p1431_1]
                        · have p1431_0 := h1431c.1
                          have p1431_1 := h1431c.2.1
                          have p1431_2 := h1431c.2.2.1
                          have p1431_3 := h1431c.2.2.2
                          linarith only [hlam, p1431_0]
                · linarith only [h0, h1, h1341, h1419, h1420, h1424, hc12, hlam, hphi, u2elo4]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1458 | h1458
            · linarith only [h1419, h1458, h912, hc03, hc34, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1460 | h1460
              · linarith only [h0, h1196, h1460, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h1462 | h1462
                · linarith only [h1341, h1419, h1462, hc12, hlam, hphi, u2elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h1464 | h1464
                  · linarith only [h1462, h1464, h912, hc03, hc34, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1466 | h1466
                    · linarith only [h1341, h1419, h1460, h1466, hc12, hlam, hphi, u2elo3]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1468 | h1468
                      · linarith only [h1341, h1462, h1466, h1468, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h1341, h1462, h1468, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 5216000 in
theorem r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo3 := h2elo (m.d 2 4) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h1 | h1
  · exact r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x0_x0 m hb1 hb2 hb4 hb5 h0 h1
  · exact r1l7_11_12_14_25_L_I_L_0_L_I_H_I_x0_x1 m hb1 hb2 hb4 hb5 h0 h1

end R2N4
