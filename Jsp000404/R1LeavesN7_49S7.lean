import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_49S6

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5720000 in
set_option maxHeartbeats 5720000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h934 | h934
  · rcases m.htr 0 1 5 (by decide) (by decide) with h935 | h935
    · rcases m.htr 0 2 3 (by decide) (by decide) with h936 | h936
      · linarith only [h0, h1, h936, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h938 | h938
        · rcases m.htr 0 2 5 (by decide) (by decide) with h939 | h939
          · rcases m.htr 0 3 4 (by decide) (by decide) with h940 | h940
            · rcases m.htr 0 3 5 (by decide) (by decide) with h941 | h941
              · rcases m.htr 0 4 5 (by decide) (by decide) with h942 | h942
                · rcases m.htr 1 2 4 (by decide) (by decide) with h943 | h943
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h944 | h944
                    · linarith only [h0, h1, h943, h944, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h936, h941, h944, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h936, h938, h943, hc12, hc23, hlam, hphi]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h948 | h948
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h949 | h949
                    · linarith only [h0, h1, h948, h949, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h936, h939, h941, h949, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h936, h938, h948, hc12, hc23, hlam, hphi]
              · linarith only [h940, h941, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h934, h940, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h955 | h955
            · rcases m.htr 0 3 5 (by decide) (by decide) with h956 | h956
              · rcases m.htr 0 4 5 (by decide) (by decide) with h957 | h957
                · linarith only [h938, h939, h957, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h959 | h959
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h960 | h960
                    · linarith only [h0, h1, h959, h960, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h936, h956, h960, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h936, h938, h959, hc12, hc23, hlam, hphi]
              · linarith only [h955, h956, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h934, h955, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h966 | h966
          · rcases m.htr 0 3 4 (by decide) (by decide) with h967 | h967
            · rcases m.htr 0 3 5 (by decide) (by decide) with h968 | h968
              · rcases m.htr 0 4 5 (by decide) (by decide) with h969 | h969
                · rcases m.htr 1 2 4 (by decide) (by decide) with h970 | h970
                  · linarith only [h0, h1, h938, h970, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h972 | h972
                    · rcases h0bigk with h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c | h973c
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [hlam, p973_0]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [h1, h966, h968, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p973_1, u3ehi4]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [h1, hlam, p973_0]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [h1, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p973_1]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [h1, h968, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p973_1, u3ehi4]
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
                        linarith only [h936, hlam, p973_0]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [h938, hlam, p973_1]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [h968, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p973_1, u3ehi4]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p973_1]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [h936, hc02, hc23, hlam, hphi, p973_1]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [hlam, p973_0]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [h936, h938, h966, h968, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p973_1, u3ehi4]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [h936, h968, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p973_1, u3ehi4]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [h934, hlam, p973_0]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [h966, h968, hc04, hlam, hphi, ht0b, ht34, ht45, ht5b, p973_1, u3ehi4]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [h967, hlam, p973_0]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [hlam, p973_0]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [h1, h934, h968, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p973_1, u3ehi4]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [h935, hlam, p973_0]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [h966, hlam, p973_1]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [h968, hlam, p973_0]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [h969, hlam, p973_1]
                      · have p973_0 := h973c.1
                        have p973_1 := h973c.2.1
                        have p973_2 := h973c.2.2.1
                        have p973_3 := h973c.2.2.2
                        linarith only [hlam, p973_0]
                    · linarith only [h936, h966, h968, h972, hc34, hlam, hphi, u3ehi4]
                · linarith only [h938, h966, h969, hlam]
              · linarith only [h967, h968, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h934, h967, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1003 | h1003
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1004 | h1004
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1005 | h1005
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1006 | h1006
                  · linarith only [h0, h1, h1006, h936, h938, hc02, hc23, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1008 | h1008
                    · rcases h0bigk with h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [hlam, p1009_0]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h0, h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1009_1]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h1, hlam, p1009_0]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h1, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1009_1]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h1, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p1009_1]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h0, hlam, p1009_0]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [hlam, p1009_0]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h936, hlam, p1009_0]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h938, hlam, p1009_1]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h966, hlam, p1009_0]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h936, hc01, hc23, hlam, hphi, ht12, p1009_1]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h0, h936, hc12, hc23, hlam, hphi, p1009_1]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [hlam, p1009_0]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h1005, h936, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1009_1]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h1004, h936, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1009_1, u3ehi4]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h934, hlam, p1009_0]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h0, h1, h934, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1009_1]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h1003, hlam, p1009_0]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [hlam, p1009_0]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h1, h1004, h934, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1009_1, u3ehi4]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h935, hlam, p1009_0]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h0, h966, hc12, hc25, hlam, hphi, p1009_1]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h1004, hlam, p1009_0]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [h1005, hlam, p1009_1]
                      · have p1009_0 := h1009c.1
                        have p1009_1 := h1009c.2.1
                        have p1009_2 := h1009c.2.2.1
                        have p1009_3 := h1009c.2.2.2
                        linarith only [hlam, p1009_0]
                    · linarith only [h1003, h1008, h936, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1036 | h1036
                  · linarith only [h0, h1036, h938, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1038 | h1038
                    · rcases h0bigk with h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c | h1039c
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [hlam, p1039_0]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h0, h1, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1039_1]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h1, hlam, p1039_0]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h1, h1003, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1039_1, u3ehi3]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h1, hc05, hc13, hlam, hphi, ht01, ht0b, ht5b, p1039_1]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h0, hlam, p1039_0]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [hlam, p1039_0]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h936, hlam, p1039_0]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h938, hlam, p1039_1]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h966, hlam, p1039_0]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h936, hc01, hc23, hlam, hphi, ht12, p1039_1]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h0, h936, hc12, hc23, hlam, hphi, p1039_1]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [hlam, p1039_0]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h1003, h936, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1039_1, u3ehi3]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h0, h936, h966, hc12, hc23, hlam, hphi, p1039_1]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h934, hlam, p1039_0]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h0, h1, h934, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1039_1]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h1003, hlam, p1039_0]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [hlam, p1039_0]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h1005, hlam, p1039_0]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h935, hlam, p1039_0]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h0, h1005, hc12, hc45, hlam, hphi, ht23, ht34, p1039_1]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h1004, hlam, p1039_0]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [h1, h935, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1039_1]
                      · have p1039_0 := h1039c.1
                        have p1039_1 := h1039c.2.1
                        have p1039_2 := h1039c.2.2.1
                        have p1039_3 := h1039c.2.2.2
                        linarith only [hlam, p1039_0]
                    · linarith only [h1, h1003, h1038, h934, h936, hlam]
              · linarith only [h1003, h1004, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h1003, h934, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1068 | h1068
      · linarith only [h0, h1, h1068, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1070 | h1070
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1071 | h1071
          · linarith only [h0, h1071, h935, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1073 | h1073
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1074 | h1074
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1075 | h1075
                · linarith only [h0, h1070, h1075, h935, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1077 | h1077
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1078 | h1078
                    · linarith only [h0, h1077, h1078, h935, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h1068, h1074, h1078, hc34, hlam, hphi, u3ehi4]
                  · linarith only [h1068, h1070, h1077, hc12, hc23, hlam, hphi]
              · linarith only [h1073, h1074, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h1073, h934, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1084 | h1084
          · linarith only [h0, h1084, h935, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1086 | h1086
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1087 | h1087
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1088 | h1088
                · linarith only [h1088, h934, h935, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1090 | h1090
                  · linarith only [h0, h1070, h1090, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1092 | h1092
                    · rcases h0bigk with h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c | h1093c
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [hlam, p1093_0]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h1068, h1087, h935, hc02, hc23, hlam, hphi, p1093_1]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h1, hlam, p1093_0]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h1, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1093_1]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h935, hlam, p1093_1]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h0, hlam, p1093_0]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [hlam, p1093_0]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h1068, hlam, p1093_0]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h1070, hlam, p1093_1]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h1084, hlam, p1093_0]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h1068, hc01, hc23, hlam, hphi, ht12, p1093_1]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h0, h1068, hc12, hc23, hlam, hphi, p1093_1]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [hlam, p1093_0]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h1068, h1086, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1093_1, u3ehi3]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h0, h1068, h935, hc12, hc23, hlam, hphi, p1093_1]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h934, hlam, p1093_0]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h0, h1, h934, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1093_1]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h1086, hlam, p1093_0]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [hlam, p1093_0]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h1088, hlam, p1093_0]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1093_1]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h0, h1084, hc12, hc25, hlam, hphi, p1093_1]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h1087, hlam, p1093_0]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [h1086, h1088, hc45, hlam, hphi, ht34, p1093_1, u3ehi3]
                      · have p1093_0 := h1093c.1
                        have p1093_1 := h1093c.2.1
                        have p1093_2 := h1093c.2.2.1
                        have p1093_3 := h1093c.2.2.2
                        linarith only [hlam, p1093_0]
                    · linarith only [h1068, h1087, h1092, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1086, h1087, hc35, hlam, hphi, u3ehi3]
            · linarith only [h1, h1086, h934, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1122 | h1122
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1123 | h1123
      · linarith only [h0, h1, h1123, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1125 | h1125
        · linarith only [h0, h1125, h934, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1127 | h1127
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1128 | h1128
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1129 | h1129
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1130 | h1130
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1131 | h1131
                  · linarith only [h0, h1, h1125, h1131, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1133 | h1133
                    · rcases h0bigk with h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c | h1134c
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [hlam, p1134_0]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1127, h1129, h1131, h1133, h934, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1134_1, u3ehi4]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1, hlam, p1134_0]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h934, hlam, p1134_1]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1129, h1131, h1133, h934, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1134_1, u3ehi4]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h0, hlam, p1134_0]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [hlam, p1134_0]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1123, hlam, p1134_0]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1125, hlam, p1134_1]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1129, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p1134_1, u3ehi4]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h0, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1134_1]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1123, hc02, hc23, hlam, hphi, p1134_1]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [hlam, p1134_0]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h0, h1123, h934, hc12, hc23, hlam, hphi, p1134_1]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1123, h1129, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1134_1, u3ehi4]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1134_1]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1131, h934, hc02, hc24, hlam, hphi, p1134_1]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1128, hlam, p1134_0]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [hlam, p1134_0]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1129, h1131, h934, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1134_1, u3ehi4]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1122, hlam, p1134_0]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1127, hlam, p1134_1]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1129, hlam, p1134_0]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [h1130, hlam, p1134_1]
                      · have p1134_0 := h1134c.1
                        have p1134_1 := h1134c.2.1
                        have p1134_2 := h1134c.2.2.1
                        have p1134_3 := h1134c.2.2.2
                        linarith only [hlam, p1134_0]
                    · linarith only [h1123, h1128, h1133, hlam]
                · linarith only [h1122, h1130, h934, hlam]
              · linarith only [h1128, h1129, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1163 | h1163
              · linarith only [h1128, h1163, hc34, hlam, hphi, u3ehi4]
              · linarith only [h0, h1, h1127, h1163, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1166 | h1166
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1167 | h1167
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1168 | h1168
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1169 | h1169
                  · linarith only [h0, h1125, h1169, h934, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1171 | h1171
                    · rcases h0bigk with h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c | h1172c
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [hlam, p1172_0]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h0, h1169, h1171, h934, hc12, hc23, hlam, hphi, p1172_1]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h1, hlam, p1172_0]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h934, hlam, p1172_1]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h1169, h1171, h934, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1172_1]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h0, hlam, p1172_0]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [hlam, p1172_0]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h1123, hlam, p1172_0]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h1125, hlam, p1172_1]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h1127, hlam, p1172_0]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h1122, hc03, hc15, hlam, hphi, ht0b, ht5b, p1172_1]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h0, h1123, hc12, hc23, hlam, hphi, p1172_1]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [hlam, p1172_0]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h0, h1123, h934, hc12, hc23, hlam, hphi, p1172_1]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h0, h1123, h1127, hc12, hc23, hlam, hphi, p1172_1]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1172_1]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h0, h1169, h1171, h934, hc12, hc23, hlam, hphi, p1172_1]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h1166, hlam, p1172_0]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [hlam, p1172_0]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h1167, h1169, h1171, h934, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1172_1, u3ehi4]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h1122, hlam, p1172_0]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h0, h1, h1122, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1172_1]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h1167, hlam, p1172_0]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [h1168, hlam, p1172_1]
                      · have p1172_0 := h1172c.1
                        have p1172_1 := h1172c.2.1
                        have p1172_2 := h1172c.2.2.1
                        have p1172_3 := h1172c.2.2.2
                        linarith only [hlam, p1172_0]
                    · linarith only [h1123, h1166, h1171, hlam]
                · linarith only [h1122, h1168, h934, hlam]
              · linarith only [h1166, h1167, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1201 | h1201
              · linarith only [h1166, h1201, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1, h1122, h1201, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h1204 | h1204
      · linarith only [h0, h1, h1204, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h1206 | h1206
        · linarith only [h0, h1206, h934, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h1208 | h1208
          · linarith only [h0, h1122, h1208, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h1210 | h1210
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1211 | h1211
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1212 | h1212
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1213 | h1213
                  · linarith only [h0, h1122, h1206, h1213, hc02, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1215 | h1215
                    · rcases h0bigk with h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c | h1216c
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [hlam, p1216_0]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h0, h1213, h1215, h934, hc12, hc23, hlam, hphi, p1216_1]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h1, hlam, p1216_0]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h934, hlam, p1216_1]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h1122, hlam, p1216_1]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h0, hlam, p1216_0]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [hlam, p1216_0]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h1204, hlam, p1216_0]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h1206, hlam, p1216_1]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h1208, hlam, p1216_0]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h1204, hc01, hc23, hlam, hphi, ht12, p1216_1]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h0, h1204, hc12, hc23, hlam, hphi, p1216_1]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [hlam, p1216_0]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h1204, h1212, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p1216_1]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h0, h1122, h1204, hc12, hc23, hlam, hphi, p1216_1]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1216_1]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h0, h1213, h1215, h934, hc12, hc23, hlam, hphi, p1216_1]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h1210, hlam, p1216_0]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [hlam, p1216_0]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h0, h1122, h1213, h1215, h934, hc12, hc23, hlam, hphi, p1216_1]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1216_1]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h0, h1208, hc12, hc25, hlam, hphi, p1216_1]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h1211, hlam, p1216_0]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [h1212, hlam, p1216_1]
                      · have p1216_0 := h1216c.1
                        have p1216_1 := h1216c.2.1
                        have p1216_2 := h1216c.2.2.1
                        have p1216_3 := h1216c.2.2.2
                        linarith only [hlam, p1216_0]
                    · linarith only [h1204, h1210, h1215, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1243 | h1243
                  · linarith only [h0, h1212, h1243, h934, hc24, hc45, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1245 | h1245
                    · rcases h0bigk with h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c | h1246c
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [hlam, p1246_0]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h0, h934, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1, hlam, p1246_0]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h934, hlam, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1122, hlam, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h0, hlam, p1246_0]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [hlam, p1246_0]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1204, hlam, p1246_0]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1206, hlam, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1208, hlam, p1246_0]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1204, hc01, hc23, hlam, hphi, ht12, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h0, h1204, hc12, hc23, hlam, hphi, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [hlam, p1246_0]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1204, h1210, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1246_1, u3ehi3]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h0, h1122, h1204, hc12, hc23, hlam, hphi, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h0, h1243, h934, hc12, hc24, hlam, hphi, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1210, hlam, p1246_0]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [hlam, p1246_0]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1212, hlam, p1246_0]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h0, h1208, hc12, hc25, hlam, hphi, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1211, hlam, p1246_0]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [h1212, hc04, hc45, hlam, hphi, p1246_1]
                      · have p1246_0 := h1246c.1
                        have p1246_1 := h1246c.2.1
                        have p1246_2 := h1246c.2.2.1
                        have p1246_3 := h1246c.2.2.2
                        linarith only [hlam, p1246_0]
                    · linarith only [h1204, h1211, h1245, hc34, hlam, hphi, u3ehi4]
              · linarith only [h1210, h1211, hc35, hlam, hphi, u3ehi3]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h1274 | h1274
              · linarith only [h1210, h1274, hc34, hlam, hphi, u3ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h1276 | h1276
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1277 | h1277
                  · linarith only [h0, h1206, h1277, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1279 | h1279
                    · linarith only [h0, h1, h1210, h1279, hc12, hc23, hlam, hphi]
                    · rcases h0bigk with h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c | h1281c
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [hlam, p1281_0]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h0, h1, h1204, hc12, hc23, hlam, hphi, p1281_1]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h1, hlam, p1281_0]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h934, hlam, p1281_1]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h1122, hlam, p1281_1]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h0, hlam, p1281_0]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [hlam, p1281_0]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h1204, hlam, p1281_0]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h1206, hlam, p1281_1]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h1208, hlam, p1281_0]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h1204, hc01, hc23, hlam, hphi, ht12, p1281_1]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h0, h1274, hc12, hc35, hlam, hphi, ht23, p1281_1]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [hlam, p1281_0]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h1210, hlam, p1281_1]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h1274, hlam, p1281_1]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h0, h1277, h1279, h934, hc12, hc34, hlam, hphi, ht23, p1281_1]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h0, h1277, h1279, h934, hc12, hc34, hlam, hphi, ht23, p1281_1]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h1277, h1279, h934, hc34, hlam, hphi, p1281_1, u3ehi0]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [hlam, p1281_0]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h0, h1, h1274, h1277, h1279, h934, hc12, hc34, hlam, hphi, ht23, p1281_1]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h0, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1281_1]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h0, h1208, hc12, hc25, hlam, hphi, p1281_1]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h0, h1, h1274, hc12, hc35, hlam, hphi, ht23, p1281_1]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [h1276, hlam, p1281_1]
                      · have p1281_0 := h1281c.1
                        have p1281_1 := h1281c.2.1
                        have p1281_2 := h1281c.2.2.1
                        have p1281_3 := h1281c.2.2.2
                        linarith only [hlam, p1281_0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h1307 | h1307
                  · linarith only [h0, h1276, h1307, h934, hc24, hc45, hlam, hphi]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h1309 | h1309
                    · linarith only [h0, h1, h1210, h1309, hc12, hc23, hlam, hphi]
                    · rcases h0bigk with h1311c | h1311c | h1311c | h1311c | h1311c | h1311c | h1311c | h1311c | h1311c | h1311c | h1311c | h1311c | h1311c | h1311c | h1311c | h1311c | h1311c | h1311c | h1311c | h1311c | h1311c | h1311c | h1311c | h1311c | h1311c
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [hlam, p1311_0]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h0, h934, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1311_1]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h1, hlam, p1311_0]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h934, hlam, p1311_1]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h1122, hlam, p1311_1]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h0, hlam, p1311_0]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [hlam, p1311_0]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h1204, hlam, p1311_0]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h1206, hlam, p1311_1]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h1208, hlam, p1311_0]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h1204, hc01, hc23, hlam, hphi, ht12, p1311_1]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h0, h1204, h1309, hc12, hc34, hlam, hphi, ht23, p1311_1]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [hlam, p1311_0]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h1210, hlam, p1311_1]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h1274, hlam, p1311_1]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h0, h1276, hc12, hc45, hlam, hphi, ht23, ht34, p1311_1]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h0, h1276, hc12, hc45, hlam, hphi, ht23, ht34, p1311_1]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h1276, hc45, hlam, hphi, ht34, p1311_1, u3ehi0]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [hlam, p1311_0]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h1276, hlam, p1311_0]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h0, h1276, hc12, hc45, hlam, hphi, ht23, ht34, p1311_1]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h0, h1276, hc12, hc45, hlam, hphi, ht23, ht34, p1311_1]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h0, h1, h1276, hc12, hc45, hlam, hphi, ht23, ht34, p1311_1]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [h1276, hc04, hc45, hlam, hphi, p1311_1]
                      · have p1311_0 := h1311c.1
                        have p1311_1 := h1311c.2.1
                        have p1311_2 := h1311c.2.2.1
                        have p1311_3 := h1311c.2.2.2
                        linarith only [hlam, p1311_0]

set_option maxHeartbeats 5720000 in
set_option maxHeartbeats 5720000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x0_x0 m hb0 hb1 hb3 hb4 h0 h1
  · exact r1l7_20_11_13_14_H_I_L_I_L_R_L_I_x0_x1 m hb0 hb1 hb3 hb4 h0 h1

end R2N4
