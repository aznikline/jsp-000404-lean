import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_55S12

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4338000 in
set_option maxHeartbeats 4338000 in
theorem r1l7_21_14_H_I_L_R_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_21_14_H_I_L_R_x0_x0_x0 m hb1 hb4 h0 h1 h2
  · exact r1l7_21_14_H_I_L_R_x0_x0_x1 m hb1 hb4 h0 h1 h2

set_option maxHeartbeats 4338000 in
set_option maxHeartbeats 4338000 in
theorem r1l7_21_14_H_I_L_R_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h941 | h941
  · rcases m.htr 0 1 5 (by decide) (by decide) with h942 | h942
    · rcases m.htr 1 2 3 (by decide) (by decide) with h943 | h943
      · linarith only [h0, h1, h943, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h945 | h945
        · linarith only [h0, h1, h943, h945, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h947 | h947
          · rcases m.htr 1 3 4 (by decide) (by decide) with h948 | h948
            · rcases m.htr 1 3 5 (by decide) (by decide) with h949 | h949
              · rcases m.htr 1 4 5 (by decide) (by decide) with h950 | h950
                · linarith only [h1, h941, h943, h950, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h945, h947, h950, hlam]
              · linarith only [h0, h1, h949, hc12, hc35, hlam, hphi, ht23]
            · linarith only [h1, h941, h948, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h955 | h955
            · rcases m.htr 1 3 5 (by decide) (by decide) with h956 | h956
              · rcases m.htr 1 4 5 (by decide) (by decide) with h957 | h957
                · linarith only [h1, h941, h957, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                · rcases h1bigk with h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c | h959c
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h1, h943, hc12, hc23, hlam, hphi, p959_1]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h1, hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h1, h943, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p959_1, u4ehi1]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h1, h943, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p959_1]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h0, hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h943, hlam, p959_1]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h945, hlam, p959_1]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h947, hlam, p959_1]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h943, hc01, hc23, hlam, hphi, ht12, p959_1]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h943, hc12, hc23, hlam, hphi, p959_1]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h943, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p959_1, u4ehi1]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h943, h947, hc12, hc23, hlam, hphi, p959_1]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h941, hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h941, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p959_1]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h955, hlam, p959_1]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h957, hlam, p959_1]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h942, hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h1, h942, h943, hc12, hc23, hlam, hphi, p959_1]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h956, hlam, p959_0]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [h1, h942, h943, h955, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p959_1, u4ehi3]
                  · have p959_0 := h959c.1
                    have p959_1 := h959c.2.1
                    have p959_2 := h959c.2.2.1
                    have p959_3 := h959c.2.2.2
                    linarith only [hlam, p959_0]
              · linarith only [h0, h1, h956, hc12, hc35, hlam, hphi, ht23]
            · linarith only [h1, h941, h955, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h987 | h987
      · linarith only [h0, h1, h987, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h989 | h989
        · linarith only [h0, h1, h989, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h991 | h991
          · linarith only [h941, h942, h989, h991, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h993 | h993
            · rcases m.htr 1 3 5 (by decide) (by decide) with h994 | h994
              · rcases m.htr 1 4 5 (by decide) (by decide) with h995 | h995
                · linarith only [h941, h942, h987, h994, h995, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h941, h942, h995, hc45, hlam, hphi, u4ehi1]
              · linarith only [h1, h941, h993, h994, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
            · linarith only [h1, h941, h993, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1000 | h1000
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1001 | h1001
      · linarith only [h0, h1, h1001, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1003 | h1003
        · linarith only [h0, h1, h1003, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1005 | h1005
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1006 | h1006
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1007 | h1007
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1008 | h1008
                · rcases h1bigk with h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c | h1009c
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [hlam, p1009_0]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [h1001, h1006, h941, hc12, hc23, hlam, hphi, p1009_1]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [h1, hlam, p1009_0]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [h941, hlam, p1009_0]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [h1001, h1006, h1008, h941, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1009_1, u4ehi4]
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
                    linarith only [h1001, hlam, p1009_1]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [h1003, hlam, p1009_1]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [h1008, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1009_1, u4ehi4]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [h1001, hc01, hc23, hlam, hphi, ht12, p1009_1]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [h1001, hc12, hc23, hlam, hphi, p1009_1]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [hlam, p1009_0]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [h1001, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1009_1, u4ehi1]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [h1001, h1008, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1009_1, u4ehi4]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [h0, h1005, h1008, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1009_1, u4ehi4]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [h1003, h1005, h1008, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1009_1, u4ehi4]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [h1006, hlam, p1009_1]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [hlam, p1009_0]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [h1001, h1006, h1008, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1009_1, u4ehi4]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [h1000, hlam, p1009_0]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [h1005, hlam, p1009_0]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [h1007, hlam, p1009_0]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [h1008, hlam, p1009_0]
                  · have p1009_0 := h1009c.1
                    have p1009_1 := h1009c.2.1
                    have p1009_2 := h1009c.2.2.1
                    have p1009_3 := h1009c.2.2.2
                    linarith only [hlam, p1009_0]
                · linarith only [h0, h1008, h941, hc12, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h0, h1, h1005, h1007, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
            · linarith only [h0, h1, h1005, h1006, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1038 | h1038
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1039 | h1039
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1040 | h1040
                · rcases h1bigk with h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c | h1041c
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [hlam, p1041_0]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [h1038, h941, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1041_1]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [h1, hlam, p1041_0]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [h941, hlam, p1041_0]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [h1038, h941, hc13, hc15, hlam, hphi, ht01, ht0b, ht5b, p1041_1]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [h0, hlam, p1041_0]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [hlam, p1041_0]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [h1001, hlam, p1041_1]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [h1003, hlam, p1041_1]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [h1005, hlam, p1041_1]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [hc01, hc13, hlam, hphi, p1041_1]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [h1001, hc12, hc23, hlam, hphi, p1041_1]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [hlam, p1041_0]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [h1001, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1041_1, u4ehi1]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [h1001, h1005, hc12, hc23, hlam, hphi, p1041_1]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [h1000, h1005, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1041_1]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [h1003, hc12, hc24, hlam, hphi, p1041_1]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [h1038, hlam, p1041_1]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [hlam, p1041_0]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [h1001, h1005, h1038, hc12, hc23, hlam, hphi, p1041_1]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [h1000, hlam, p1041_0]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [h1000, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1041_1]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [h1039, hlam, p1041_0]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [h1040, hlam, p1041_0]
                  · have p1041_0 := h1041c.1
                    have p1041_1 := h1041c.2.1
                    have p1041_2 := h1041c.2.2.1
                    have p1041_3 := h1041c.2.2.2
                    linarith only [hlam, p1041_0]
                · linarith only [h0, h1040, h941, hc12, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h1, h1000, h1005, h1039, hc12, hc35, hlam, hphi, ht23]
            · linarith only [h1, h1000, h1005, h1038, hc12, hc34, hlam, hphi, ht23]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1070 | h1070
      · linarith only [h0, h1, h1070, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1072 | h1072
        · linarith only [h0, h1, h1070, h1072, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1074 | h1074
          · linarith only [h0, h1000, h1074, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1076 | h1076
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1077 | h1077
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1078 | h1078
                · rcases h1bigk with h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c | h1079c
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [hlam, p1079_0]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h1000, h1070, h1076, h1078, hc12, hc23, hlam, hphi, p1079_1]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h1, hlam, p1079_0]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h941, hlam, p1079_0]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h1000, hlam, p1079_0]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h0, hlam, p1079_0]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [hlam, p1079_0]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h1070, hlam, p1079_1]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h1072, hlam, p1079_1]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h1074, hlam, p1079_1]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h1070, hc01, hc23, hlam, hphi, ht12, p1079_1]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h1070, hc12, hc23, hlam, hphi, p1079_1]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [hlam, p1079_0]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h1070, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1079_1, u4ehi1]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h0, h1000, h1070, hc12, hc23, hlam, hphi, p1079_1]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h0, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1079_1]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h1072, hc12, hc24, hlam, hphi, p1079_1]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h1076, hlam, p1079_1]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [hlam, p1079_0]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h0, h1000, h1070, h1076, hc12, hc23, hlam, hphi, p1079_1]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1079_1]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h1074, hc12, hc25, hlam, hphi, p1079_1]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h1077, hlam, p1079_0]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [h1078, hlam, p1079_0]
                  · have p1079_0 := h1079c.1
                    have p1079_1 := h1079c.2.1
                    have p1079_2 := h1079c.2.2.1
                    have p1079_3 := h1079c.2.2.2
                    linarith only [hlam, p1079_0]
                · linarith only [h0, h1078, h941, hc12, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h0, h1, h1077, hc12, hc35, hlam, hphi, ht23]
            · linarith only [h0, h1, h1076, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 4338000 in
set_option maxHeartbeats 4338000 in
theorem r1l7_21_14_H_I_L_R_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_21_14_H_I_L_R_x0_x0 m hb1 hb4 h0 h1
  · exact r1l7_21_14_H_I_L_R_x0_x1 m hb1 hb4 h0 h1

set_option maxHeartbeats 4338000 in
set_option maxHeartbeats 4338000 in
theorem r1l7_21_14_H_I_L_R_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1108 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1109 | h1109
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1110 | h1110
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1111 | h1111
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1112 | h1112
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1113 | h1113
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1114 | h1114
            · linarith only [h0, h1108, h1114, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1116 | h1116
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1117 | h1117
                · linarith only [h0, h1109, h1117, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                · linarith only [h1114, h1116, h1117, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1120 | h1120
                · linarith only [h0, h1109, h1120, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                · rcases h1bigk with h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c | h1122c
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h0, hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h0, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1122_1, u4ehi1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [hc01, hc12, hlam, hphi, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    rcases p1122_3 (m.d 0 1) (by simp) with h1130 | h1130
                    · linarith only [h0, h1130, hlam]
                    · linarith only [h1108, h1130, hlam]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h1112, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1122_1, u4ehi2]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h1112, h1120, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1122_1, u4ehi2]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h1108, hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h1111, hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h1114, hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h1116, hlam, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h1109, hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h1112, hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h1110, h1111, h1120, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h1120, hlam, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h1110, hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h1113, hlam, p1122_0]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h0, h1110, h1111, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1122_1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [h0, h1110, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1122_1, u4ehi1]
                  · have p1122_0 := h1122c.1
                    have p1122_1 := h1122c.2.1
                    have p1122_2 := h1122c.2.2.1
                    have p1122_3 := h1122c.2.2.2
                    linarith only [hlam, p1122_0]
          · linarith only [h0, h1109, h1112, h1113, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
        · linarith only [h0, h1109, h1112, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
      · linarith only [h0, h1109, h1111, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1153 | h1153
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1154 | h1154
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1155 | h1155
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1156 | h1156
            · linarith only [h1108, h1110, h1155, h1156, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1158 | h1158
              · linarith only [h1109, h1110, h1156, h1158, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1160 | h1160
                · linarith only [h1109, h1110, h1158, h1160, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                · linarith only [h1109, h1110, h1160, hc45, hlam, hphi, u4ehi1]
          · linarith only [h0, h1109, h1154, h1155, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
        · linarith only [h0, h1109, h1154, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
      · linarith only [h0, h1109, h1153, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1166 | h1166
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1167 | h1167
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1168 | h1168
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1169 | h1169
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1170 | h1170
            · linarith only [h1108, h1109, h1168, h1170, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1172 | h1172
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1173 | h1173
                · rcases h1bigk with h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c | h1174c
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h0, hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1109, h1170, hc13, hc34, hlam, hphi, p1174_1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1109, hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1109, h1170, h1173, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1174_1, u4ehi4]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [hc01, hc12, hlam, hphi, p1174_1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1172, h1173, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1174_1, u4ehi4]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1174_1, u4ehi1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1173, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1174_1, u4ehi4]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1108, hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1167, hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1170, hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1108, h1173, hc01, hlam, hphi, ht0b, ht45, ht5b, p1174_1, u4ehi4]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [hc01, hc14, hlam, hphi, p1174_1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1168, hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1167, h1170, hc23, hc34, hlam, hphi, p1174_1]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1170, h1173, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1174_1, u4ehi4]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1166, hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1169, hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1172, hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [h1173, hlam, p1174_0]
                  · have p1174_0 := h1174c.1
                    have p1174_1 := h1174c.2.1
                    have p1174_2 := h1174c.2.2.1
                    have p1174_3 := h1174c.2.2.2
                    linarith only [hlam, p1174_0]
                · linarith only [h1108, h1109, h1173, hc13, hc45, hlam, hphi, ht34]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1201 | h1201
                · rcases h1bigk with h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c | h1202c
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [hlam, p1202_0]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [h0, hlam, p1202_0]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [h1109, h1167, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1202_1]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [h1109, hlam, p1202_0]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [h1109, h1201, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1202_1, u4ehi4]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [hc01, hc12, hlam, hphi, p1202_1]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [hlam, p1202_0]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    rcases p1202_3 (m.d 0 1) (by simp) with h1210 | h1210
                    · linarith only [h0, h1210, hlam]
                    · linarith only [h1108, h1210, hlam]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [h1109, h1166, h1201, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1202_1, u4ehi4]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [h1201, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1202_1, u4ehi4]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [h1108, hlam, p1202_0]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [h1167, hlam, p1202_0]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [hlam, p1202_0]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [h1170, hlam, p1202_0]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [h1172, hlam, p1202_1]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [h1166, h1170, h1201, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1202_1, u4ehi4]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [h1168, hlam, p1202_0]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [h1167, h1170, hc23, hc34, hlam, hphi, p1202_1]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [hlam, p1202_0]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [h1170, h1201, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p1202_1, u4ehi4]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [h1166, hlam, p1202_0]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [h1169, hlam, p1202_0]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [h1166, h1167, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1202_1]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [h1201, hlam, p1202_0]
                  · have p1202_0 := h1202c.1
                    have p1202_1 := h1202c.2.1
                    have p1202_2 := h1202c.2.2.1
                    have p1202_3 := h1202c.2.2.2
                    linarith only [hlam, p1202_0]
                · linarith only [h1108, h1109, h1167, h1201, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h1109, h1166, h1168, h1169, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1232 | h1232
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1233 | h1233
            · linarith only [h0, h1108, h1168, h1233, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1235 | h1235
              · linarith only [h0, h1108, h1168, h1235, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1237 | h1237
                · linarith only [h0, h1166, h1168, h1237, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                · linarith only [h1109, h1166, h1167, h1235, h1237, hc23, hc45, hlam, hphi, ht34]
          · linarith only [h0, h1166, h1232, hlam]
      · linarith only [h0, h1108, h1167, hlam]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1242 | h1242
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1243 | h1243
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1244 | h1244
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1245 | h1245
            · linarith only [h1108, h1166, h1245, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1247 | h1247
              · linarith only [h1108, h1166, h1247, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1249 | h1249
                · rcases h1bigk with h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c | h1250c
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [hlam, p1250_0]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [h0, hlam, p1250_0]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [h1166, h1245, h1249, hc13, hc34, hlam, hphi, p1250_1]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [h1109, hlam, p1250_0]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [h1166, hlam, p1250_0]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [hc01, hc12, hlam, hphi, p1250_1]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [hlam, p1250_0]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    rcases p1250_3 (m.d 0 1) (by simp) with h1258 | h1258
                    · linarith only [h0, h1258, hlam]
                    · linarith only [h1108, h1258, hlam]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [h1109, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1250_1, u4ehi0]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [h1108, h1166, h1242, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1250_1]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [h1108, hlam, p1250_0]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [h1242, hlam, p1250_0]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [hlam, p1250_0]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [h1245, hlam, p1250_0]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [h1247, hlam, p1250_1]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [h1108, h1242, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1250_1]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [h1243, hlam, p1250_0]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [h1242, h1245, hc23, hc34, hlam, hphi, p1250_1]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [hlam, p1250_0]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [h1108, h1166, h1242, h1245, hc23, hc34, hlam, hphi, p1250_1]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [h1108, h1242, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1250_1]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [h1244, hlam, p1250_0]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [h1242, h1247, hc23, hc35, hlam, hphi, p1250_1]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [h1249, hlam, p1250_0]
                  · have p1250_0 := h1250c.1
                    have p1250_1 := h1250c.2.1
                    have p1250_2 := h1250c.2.2.1
                    have p1250_3 := h1250c.2.2.2
                    linarith only [hlam, p1250_0]
                · linarith only [h1108, h1109, h1242, h1249, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1279 | h1279
            · linarith only [h1108, h1109, h1279, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1281 | h1281
              · linarith only [h1108, h1109, h1243, h1244, h1281, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1283 | h1283
                · linarith only [h1243, h1244, h1283, hlam]
                · linarith only [h1108, h1109, h1283, hc13, hc45, hlam, hphi, ht34]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1286 | h1286
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1287 | h1287
            · linarith only [h1108, h1166, h1286, h1287, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1289 | h1289
              · linarith only [h1108, h1166, h1243, h1286, h1289, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1291 | h1291
                · rcases h1bigk with h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c | h1292c
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [hlam, p1292_0]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h0, hlam, p1292_0]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h1166, h1243, h1286, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1292_1]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h1109, hlam, p1292_0]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h1166, hlam, p1292_0]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h1243, hc01, hc24, hlam, hphi, ht12, p1292_1]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [hlam, p1292_0]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h1242, h1243, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1292_1]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h1243, hlam, p1292_1]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h1243, hc15, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1292_1]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h1108, hlam, p1292_0]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h1242, hlam, p1292_0]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [hlam, p1292_0]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h1287, hlam, p1292_0]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h1289, hlam, p1292_1]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h1108, h1242, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1292_1]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h0, h1287, hc02, hc34, hlam, hphi, ht23, p1292_1]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h1242, h1287, hc23, hc34, hlam, hphi, p1292_1]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [hlam, p1292_0]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h1108, h1166, h1242, h1287, hc23, hc34, hlam, hphi, p1292_1]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h1108, h1242, h1243, h1286, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1292_1]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h1286, hlam, p1292_0]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h1242, h1243, h1286, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1292_1]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [h1291, hlam, p1292_0]
                  · have p1292_0 := h1292c.1
                    have p1292_1 := h1292c.2.1
                    have p1292_2 := h1292c.2.2.1
                    have p1292_3 := h1292c.2.2.2
                    linarith only [hlam, p1292_0]
                · linarith only [h1108, h1109, h1242, h1291, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1319 | h1319
            · linarith only [h0, h1108, h1243, h1319, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1321 | h1321
              · linarith only [h0, h1108, h1243, h1321, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1323 | h1323
                · rcases h1bigk with h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c | h1324c
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [hlam, p1324_0]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h0, hlam, p1324_0]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h0, h1243, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1324_1]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h1109, hlam, p1324_0]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h1166, hlam, p1324_0]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h1243, hc01, hc24, hlam, hphi, ht12, p1324_1]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [hlam, p1324_0]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h1243, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1324_1]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h1243, hlam, p1324_1]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h1286, hlam, p1324_1]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h1108, hlam, p1324_0]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h1242, hlam, p1324_0]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [hlam, p1324_0]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h1319, hlam, p1324_0]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h1321, hlam, p1324_1]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h1108, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1324_1]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h1319, hc12, hc34, hlam, hphi, ht23, p1324_1]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h1242, h1319, hc23, hc34, hlam, hphi, p1324_1]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [hlam, p1324_0]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h0, h1108, h1242, h1286, h1319, hc23, hc34, hlam, hphi, p1324_1]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h1108, h1242, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1324_1]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h0, h1108, h1242, h1321, hc23, hc35, hlam, hphi, p1324_1]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h1242, h1321, hc23, hc35, hlam, hphi, p1324_1]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [h1323, hlam, p1324_0]
                  · have p1324_0 := h1324c.1
                    have p1324_1 := h1324c.2.1
                    have p1324_2 := h1324c.2.2.1
                    have p1324_3 := h1324c.2.2.2
                    linarith only [hlam, p1324_0]
                · linarith only [h1108, h1109, h1242, h1323, hc23, hc45, hlam, hphi, ht34]
      · linarith only [h0, h1108, h1242, hlam]

set_option maxHeartbeats 4338000 in
set_option maxHeartbeats 4338000 in
theorem r1l7_21_14_H_I_L_R_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1108 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1352 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h1353 | h1353
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1354 | h1354
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1355 | h1355
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1356 | h1356
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1357 | h1357
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1358 | h1358
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1359 | h1359
              · linarith only [h1108, h1352, h1354, h1359, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
              · rcases h1bigk with h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c | h1361c
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [hlam, p1361_0]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [h0, hlam, p1361_0]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [h1108, hlam, p1361_0]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [h1108, h1354, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1361_1, u4ehi1]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [h1108, h1354, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p1361_1]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [hc01, hc12, hlam, hphi, p1361_1]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [hlam, p1361_0]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [h1108, hc01, hc12, hlam, hphi, p1361_1]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [h1357, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1361_1, u4ehi3]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [h1357, h1359, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1361_1, u4ehi3]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [h1353, h1357, h1359, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1361_1, u4ehi3]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [h1354, hlam, p1361_0]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [hlam, p1361_0]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [h1354, h1357, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1361_1, u4ehi3]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [h1354, h1357, h1359, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1361_1, u4ehi3]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [h1352, hlam, p1361_0]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [h1355, hlam, p1361_0]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [h1357, hlam, p1361_1]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [hlam, p1361_0]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [h1359, hlam, p1361_1]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [h1353, hlam, p1361_0]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [h1356, hlam, p1361_0]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [h1358, hlam, p1361_0]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [h1353, h1357, hc01, hlam, hphi, ht0b, ht45, ht5b, p1361_1, u4ehi3]
                · have p1361_0 := h1361c.1
                  have p1361_1 := h1361c.2.1
                  have p1361_2 := h1361c.2.2.1
                  have p1361_3 := h1361c.2.2.2
                  linarith only [hlam, p1361_0]
            · linarith only [h1108, h1352, h1357, h1358, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
          · linarith only [h1108, h1352, h1357, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
        · linarith only [h1108, h1352, h1354, h1355, h1356, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
      · linarith only [h1108, h1352, h1354, h1355, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
    · linarith only [h0, h1352, h1354, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h1392 | h1392
    · rcases m.htr 1 2 4 (by decide) (by decide) with h1393 | h1393
      · rcases m.htr 1 2 5 (by decide) (by decide) with h1394 | h1394
        · rcases m.htr 1 3 4 (by decide) (by decide) with h1395 | h1395
          · rcases m.htr 1 3 5 (by decide) (by decide) with h1396 | h1396
            · rcases m.htr 1 4 5 (by decide) (by decide) with h1397 | h1397
              · linarith only [h1352, h1353, h1392, h1396, h1397, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
              · linarith only [h1352, h1353, h1397, hc45, hlam, hphi, u4ehi1]
            · linarith only [h1108, h1352, h1395, h1396, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
          · linarith only [h1108, h1352, h1393, h1395, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
        · linarith only [h1108, h1352, h1392, h1393, h1394, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
      · linarith only [h1108, h1352, h1392, h1393, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
    · linarith only [h0, h1352, h1392, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]

set_option maxHeartbeats 4338000 in
set_option maxHeartbeats 4338000 in
theorem r1l7_21_14_H_I_L_R_x1_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1108 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h1352 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h1405 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h4ehi := hb4.1
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 1 2 3 (by decide) (by decide) with h1406 | h1406
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1407 | h1407
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1408 | h1408
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1409 | h1409
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1410 | h1410
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1411 | h1411
            · rcases h1bigk with h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c | h1412c
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [hlam, p1412_0]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [h0, hlam, p1412_0]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [h1108, hlam, p1412_0]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [h1352, hlam, p1412_0]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [h1411, hc01, hlam, hphi, ht0b, ht45, ht5b, p1412_1, u4ehi4]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [hc01, hc12, hlam, hphi, p1412_1]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [hlam, p1412_0]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [h1409, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1412_1, u4ehi1]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [h1352, h1405, h1411, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1412_1, u4ehi4]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [h1411, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1412_1, u4ehi4]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [h1405, h1411, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p1412_1, u4ehi4]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [h1406, hlam, p1412_0]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [hlam, p1412_0]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [h1352, h1405, h1406, h1411, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1412_1, u4ehi4]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [h1406, h1411, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1412_1, u4ehi4]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [h1405, h1411, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1412_1, u4ehi4]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [h1407, hlam, p1412_0]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [h1409, hlam, p1412_1]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [hlam, p1412_0]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [h1406, h1409, h1411, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1412_1, u4ehi4]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [h1405, hlam, p1412_0]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [h1408, hlam, p1412_0]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [h1410, hlam, p1412_0]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [h1411, hlam, p1412_0]
              · have p1412_0 := h1412c.1
                have p1412_1 := h1412c.2.1
                have p1412_2 := h1412c.2.2.1
                have p1412_3 := h1412c.2.2.2
                linarith only [hlam, p1412_0]
            · linarith only [h1352, h1405, h1411, hlam]
          · linarith only [h1108, h1405, h1410, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1440 | h1440
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1441 | h1441
            · linarith only [h1108, h1405, h1409, h1441, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
            · linarith only [h1108, h1405, h1409, h1441, hlam]
          · linarith only [h1108, h1405, h1440, hlam]
      · linarith only [h1108, h1405, h1407, h1408, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1446 | h1446
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1447 | h1447
        · linarith only [h1406, h1407, h1447, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1449 | h1449
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1450 | h1450
            · linarith only [h1108, h1405, h1406, h1407, h1450, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · linarith only [h1108, h1405, h1406, h1407, h1450, hlam]
          · linarith only [h1108, h1405, h1449, hlam]
      · linarith only [h1108, h1405, h1406, h1446, hlam]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h1455 | h1455
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1456 | h1456
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1457 | h1457
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1458 | h1458
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1459 | h1459
            · linarith only [h1352, h1405, h1406, h1455, h1459, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · linarith only [h1352, h1405, h1459, hlam]
          · linarith only [h1352, h1405, h1406, h1455, h1458, hlam]
        · linarith only [h1406, h1455, h1457, hlam]
      · linarith only [h1352, h1405, h1455, h1456, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h1465 | h1465
      · rcases m.htr 1 3 4 (by decide) (by decide) with h1466 | h1466
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1467 | h1467
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1468 | h1468
            · linarith only [h0, h1405, h1455, h1468, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · linarith only [h0, h1405, h1455, h1468, hlam]
          · linarith only [h0, h1405, h1455, h1466, h1467, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h1472 | h1472
          · rcases m.htr 1 4 5 (by decide) (by decide) with h1473 | h1473
            · linarith only [h0, h1405, h1455, h1473, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
            · linarith only [h0, h1405, h1406, h1466, h1473, hlam]
          · linarith only [h0, h1405, h1406, h1472, hlam]
      · linarith only [h0, h1405, h1465, hlam]

end R2N4
