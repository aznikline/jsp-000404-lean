import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_53S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4910000 in
set_option maxHeartbeats 4910000 in
theorem r1l7_21_15_H_I_L_R_x0_x1 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5ehi := hb5.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h980 | h980
  · rcases m.htr 0 1 5 (by decide) (by decide) with h981 | h981
    · rcases m.htr 1 2 3 (by decide) (by decide) with h982 | h982
      · linarith only [h0, h1, h982, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h984 | h984
        · rcases m.htr 1 2 5 (by decide) (by decide) with h985 | h985
          · linarith only [h0, h1, h982, h985, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h987 | h987
            · rcases m.htr 1 3 5 (by decide) (by decide) with h988 | h988
              · rcases m.htr 1 4 5 (by decide) (by decide) with h989 | h989
                · linarith only [h1, h981, h982, h984, h985, h989, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases h1bigk with h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c | h991c
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h1, h982, h984, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h1, hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h1, h982, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h1, h982, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p991_1, u5ehi1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h0, hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h982, hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h985, h987, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h985, hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h982, hc01, hc23, hlam, hphi, ht12, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h982, hc12, hc23, hlam, hphi, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    rcases p991_3 (m.d 0 1) (by simp) with h1005 | h1005
                    · linarith only [h1, h1005, hlam]
                    · linarith only [h1005, h980, hlam]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h982, h984, h985, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h980, hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h984, hlam, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h987, hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h989, hlam, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h981, hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h981, h984, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h988, hlam, p991_0]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [h1, h981, h982, h987, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p991_1]
                  · have p991_0 := h991c.1
                    have p991_1 := h991c.2.1
                    have p991_2 := h991c.2.2.1
                    have p991_3 := h991c.2.2.2
                    linarith only [hlam, p991_0]
              · linarith only [h1, h981, h988, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
            · linarith only [h1, h981, h984, h985, h987, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1021 | h1021
          · linarith only [h0, h1, h1021, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1023 | h1023
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1024 | h1024
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1025 | h1025
                · linarith only [h1, h1025, h980, h982, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases h1bigk with h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c | h1027c
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [hlam, p1027_0]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h1, h982, hc12, hc23, hlam, hphi, p1027_1]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h1, hlam, p1027_0]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h1, h982, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1027_1]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h1, h982, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1027_1, u5ehi1]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h0, hlam, p1027_0]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [hlam, p1027_0]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h982, hlam, p1027_0]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h984, hlam, p1027_0]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h1021, hlam, p1027_0]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h982, hc01, hc23, hlam, hphi, ht12, p1027_1]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h982, hc12, hc23, hlam, hphi, p1027_1]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [hlam, p1027_0]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h982, h984, hc12, hc23, hlam, hphi, p1027_1]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h1024, h982, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1027_1, u5ehi3]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h980, hlam, p1027_0]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h1025, hc12, hc45, hlam, hphi, ht23, ht34, p1027_1]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h1023, hlam, p1027_0]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [hlam, p1027_0]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h1025, hlam, p1027_1]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h981, hlam, p1027_0]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h981, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1027_1]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h1024, hlam, p1027_0]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [h1, h981, h982, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1027_1]
                  · have p1027_0 := h1027c.1
                    have p1027_1 := h1027c.2.1
                    have p1027_2 := h1027c.2.2.1
                    have p1027_3 := h1027c.2.2.2
                    linarith only [hlam, p1027_0]
              · linarith only [h1, h1024, h981, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
            · linarith only [h1, h1023, h981, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1055 | h1055
      · linarith only [h0, h1, h1055, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1057 | h1057
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1058 | h1058
          · linarith only [h0, h1, h1055, h1058, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1060 | h1060
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1061 | h1061
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1062 | h1062
                · linarith only [h1055, h1061, h1062, h980, h981, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · linarith only [h0, h1057, h1062, h981, hc24, hc45, hlam, hphi]
              · linarith only [h0, h1, h1057, h1061, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · linarith only [h0, h1, h1057, h1060, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1067 | h1067
          · linarith only [h1, h1057, h1067, h980, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1069 | h1069
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1070 | h1070
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1071 | h1071
                · linarith only [h1055, h1070, h1071, h980, h981, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases h1bigk with h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c | h1073c
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [hlam, p1073_0]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [h1071, h981, hc12, hc45, hlam, hphi, ht23, ht34, p1073_1]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [h1, hlam, p1073_0]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [h1071, h981, hc14, hc45, hlam, hphi, p1073_1]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [h981, hlam, p1073_0]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [h0, hlam, p1073_0]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [hlam, p1073_0]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [h1055, hlam, p1073_0]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [h1057, hlam, p1073_0]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [h1067, hlam, p1073_0]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [h1055, hc01, hc23, hlam, hphi, ht12, p1073_1]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [h1055, hc12, hc23, hlam, hphi, p1073_1]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [hlam, p1073_0]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [h1055, h1057, hc12, hc23, hlam, hphi, p1073_1]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [h1055, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1073_1, u5ehi1]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [h980, hlam, p1073_0]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [h980, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1073_1]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [h1069, hlam, p1073_0]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [hlam, p1073_0]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [h1071, hlam, p1073_1]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [hc01, hc15, hlam, hphi, p1073_1]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [h1067, hc12, hc25, hlam, hphi, p1073_1]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [h1070, hlam, p1073_0]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [h1057, h1071, hc12, hc45, hlam, hphi, ht23, ht34, p1073_1]
                  · have p1073_0 := h1073c.1
                    have p1073_1 := h1073c.2.1
                    have p1073_2 := h1073c.2.2.1
                    have p1073_3 := h1073c.2.2.2
                    linarith only [hlam, p1073_0]
              · linarith only [h1, h1057, h1070, h980, hc12, hc35, hlam, hphi, ht23]
            · linarith only [h1, h1057, h1069, h980, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1101 | h1101
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1102 | h1102
      · linarith only [h0, h1, h1102, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1104 | h1104
        · linarith only [h0, h1104, h980, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1106 | h1106
          · linarith only [h0, h1, h1102, h1106, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1108 | h1108
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1109 | h1109
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1110 | h1110
                · rcases h1bigk with h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c | h1111c
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [hlam, p1111_0]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h1102, h1108, h980, hc12, hc23, hlam, hphi, p1111_1]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h1, hlam, p1111_0]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h980, hlam, p1111_0]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h1102, h1108, h980, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1111_1, u5ehi1]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h0, hlam, p1111_0]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [hlam, p1111_0]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h1102, hlam, p1111_0]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h1104, hlam, p1111_0]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h1106, hlam, p1111_0]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h1102, hc01, hc23, hlam, hphi, ht12, p1111_1]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h1102, hc12, hc23, hlam, hphi, p1111_1]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [hlam, p1111_0]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h1101, h1102, h1109, h980, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1111_1, u5ehi3]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h1102, h1109, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1111_1, u5ehi3]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h1101, h1109, hc14, hlam, hphi, ht01, ht0b, ht5b, p1111_1, u5ehi3]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h1104, hc12, hc24, hlam, hphi, p1111_1]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h1108, hlam, p1111_0]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [hlam, p1111_0]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h1102, h1108, h1109, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1111_1, u5ehi3]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h1101, hlam, p1111_0]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h1101, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p1111_1]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h1109, hlam, p1111_0]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [h1110, hlam, p1111_0]
                  · have p1111_0 := h1111c.1
                    have p1111_1 := h1111c.2.1
                    have p1111_2 := h1111c.2.2.1
                    have p1111_3 := h1111c.2.2.2
                    linarith only [hlam, p1111_0]
                · linarith only [h1101, h1109, h1110, h980, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
              · linarith only [h1101, h1108, h1109, h980, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
            · linarith only [h1, h1101, h1108, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1140 | h1140
      · linarith only [h0, h1, h1140, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1142 | h1142
        · linarith only [h0, h1142, h980, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1144 | h1144
          · linarith only [h0, h1, h1144, hc13, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1146 | h1146
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1147 | h1147
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1148 | h1148
                · rcases h1bigk with h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c | h1149c
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [hlam, p1149_0]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h1101, h1140, h1146, h1148, hc12, hc23, hlam, hphi, p1149_1]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h1, hlam, p1149_0]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h980, hlam, p1149_0]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h1101, hlam, p1149_0]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h0, hlam, p1149_0]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [hlam, p1149_0]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h1140, hlam, p1149_0]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h1142, hlam, p1149_0]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h1144, hlam, p1149_0]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h1140, hc01, hc23, hlam, hphi, ht12, p1149_1]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h1140, hc12, hc23, hlam, hphi, p1149_1]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [hlam, p1149_0]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h1140, h1148, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p1149_1, u5ehi1]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h0, h1101, h1140, hc12, hc23, hlam, hphi, p1149_1]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h0, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1149_1]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h1142, hc12, hc24, hlam, hphi, p1149_1]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h1146, hlam, p1149_0]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [hlam, p1149_0]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h0, h1101, h1140, h1146, hc12, hc23, hlam, hphi, p1149_1]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p1149_1]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h1144, hc12, hc25, hlam, hphi, p1149_1]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h1147, hlam, p1149_0]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [h1148, hlam, p1149_0]
                  · have p1149_0 := h1149c.1
                    have p1149_1 := h1149c.2.1
                    have p1149_2 := h1149c.2.2.1
                    have p1149_3 := h1149c.2.2.2
                    linarith only [hlam, p1149_0]
                · linarith only [h0, h1148, h980, hc12, hc45, hlam, hphi, ht23, ht34]
              · linarith only [h0, h1, h1147, hc12, hc35, hlam, hphi, ht23]
            · linarith only [h0, h1, h1146, hc12, hc34, hlam, hphi, ht23]

set_option maxHeartbeats 4910000 in
set_option maxHeartbeats 4910000 in
theorem r1l7_21_15_H_I_L_R_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h5ehi := hb5.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · exact r1l7_21_15_H_I_L_R_x0_x0 m hb1 hb5 h0 h1
  · exact r1l7_21_15_H_I_L_R_x0_x1 m hb1 hb5 h0 h1

set_option maxHeartbeats 4910000 in
set_option maxHeartbeats 4910000 in
theorem r1l7_21_15_H_I_L_R_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_R m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h1178 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h5ehi := hb5.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 4 (by decide) (by decide) with h1179 | h1179
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1180 | h1180
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1181 | h1181
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1182 | h1182
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1183 | h1183
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1184 | h1184
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1185 | h1185
              · linarith only [h0, h1178, h1185, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1187 | h1187
                · linarith only [h0, h1180, h1184, h1185, h1187, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                · rcases h1bigk with h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c | h1189c
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [hlam, p1189_0]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [h0, hlam, p1189_0]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [h0, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1189_1]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [h0, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1189_1]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p1189_1, u5ehi1]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [hc01, hc12, hlam, hphi, p1189_1]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [hlam, p1189_0]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [h1184, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1189_1]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    rcases p1189_3 (m.d 0 1) (by simp) with h1198 | h1198
                    · linarith only [h0, h1198, hlam]
                    · linarith only [h1179, h1198, hlam]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [h1184, h1185, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p1189_1]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [h1178, hlam, p1189_0]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [h1181, hlam, p1189_1]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [hlam, p1189_0]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [h1180, h1182, h1185, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p1189_1]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [h1185, hlam, p1189_1]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [h1179, hlam, p1189_0]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [h1182, hlam, p1189_1]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [h1184, hlam, p1189_0]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [hlam, p1189_0]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [h1187, hlam, p1189_1]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [h1180, hlam, p1189_0]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [h1183, hlam, p1189_1]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [h0, h1180, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p1189_1]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [h0, h1180, h1182, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p1189_1]
                  · have p1189_0 := h1189c.1
                    have p1189_1 := h1189c.2.1
                    have p1189_2 := h1189c.2.2.1
                    have p1189_3 := h1189c.2.2.2
                    linarith only [hlam, p1189_0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1217 | h1217
              · linarith only [h0, h1178, h1217, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1219 | h1219
                · linarith only [h0, h1179, h1219, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                · rcases h1bigk with h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c | h1221c
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [hlam, p1221_0]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [h0, hlam, p1221_0]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [h0, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1221_1]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [h0, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1221_1]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht5b, p1221_1, u5ehi1]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [hc01, hc12, hlam, hphi, p1221_1]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [hlam, p1221_0]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    rcases p1221_3 (m.d 0 1) (by simp) with h1229 | h1229
                    · linarith only [h0, h1229, hlam]
                    · linarith only [h1178, h1229, hlam]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    rcases p1221_3 (m.d 0 1) (by simp) with h1232 | h1232
                    · linarith only [h0, h1232, hlam]
                    · linarith only [h1179, h1232, hlam]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [h1183, hc12, hlam, hphi, ht01, ht0b, ht5b, p1221_1, u5ehi2]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [h1178, hlam, p1221_0]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [h1181, hlam, p1221_1]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [hlam, p1221_0]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [h1184, hlam, p1221_1]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [h1217, hlam, p1221_1]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [h1179, hlam, p1221_0]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [h1182, hlam, p1221_1]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [h1181, h1219, hc23, hc45, hlam, hphi, ht34, p1221_1]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [hlam, p1221_0]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [h1219, hlam, p1221_1]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [h1180, hlam, p1221_0]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [h1183, hlam, p1221_1]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [h1180, h1181, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1221_1]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [h0, h1180, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p1221_1]
                  · have p1221_0 := h1221c.1
                    have p1221_1 := h1221c.2.1
                    have p1221_2 := h1221c.2.2.1
                    have p1221_3 := h1221c.2.2.2
                    linarith only [hlam, p1221_0]
          · linarith only [h0, h1180, h1183, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
        · linarith only [h0, h1180, h1182, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
      · linarith only [h0, h1180, h1181, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1254 | h1254
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1255 | h1255
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1256 | h1256
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1257 | h1257
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1258 | h1258
              · linarith only [h1178, h1180, h1256, h1258, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1260 | h1260
                · linarith only [h1179, h1180, h1258, h1260, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · linarith only [h1178, h1180, h1257, h1260, hc34, hc45, hlam, hphi]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1263 | h1263
              · linarith only [h1179, h1180, h1256, h1257, h1263, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1265 | h1265
                · linarith only [h1179, h1180, h1263, h1265, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi4]
                · rcases h1bigk with h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c | h1267c
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [hlam, p1267_0]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [h0, hlam, p1267_0]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [h1180, h1265, hc13, hc45, hlam, hphi, ht34, p1267_1]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [h1180, h1265, hc14, hc45, hlam, hphi, p1267_1]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [h1180, hlam, p1267_0]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [hc01, hc12, hlam, hphi, p1267_1]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [hlam, p1267_0]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    rcases p1267_3 (m.d 0 1) (by simp) with h1275 | h1275
                    · linarith only [h0, h1275, hlam]
                    · linarith only [h1178, h1275, hlam]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    rcases p1267_3 (m.d 0 1) (by simp) with h1278 | h1278
                    · linarith only [h0, h1278, hlam]
                    · linarith only [h1179, h1278, hlam]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [hc12, hlam, hphi, ht01, ht0b, ht5b, p1267_1, u5ehi1]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [h1178, hlam, p1267_0]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [h1254, hlam, p1267_1]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [hlam, p1267_0]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [h1257, hlam, p1267_1]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [h1263, hlam, p1267_1]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [h1179, hlam, p1267_0]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [h1255, hlam, p1267_1]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [h1179, h1254, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1267_1]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [hlam, p1267_0]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [h1265, hlam, p1267_1]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [hc01, hc15, hlam, hphi, p1267_1]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [h1256, hlam, p1267_1]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [h1254, h1263, hc23, hc35, hlam, hphi, p1267_1]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [h1254, h1257, h1265, hc23, hc45, hlam, hphi, ht34, p1267_1]
                  · have p1267_0 := h1267c.1
                    have p1267_1 := h1267c.2.1
                    have p1267_2 := h1267c.2.2.1
                    have p1267_3 := h1267c.2.2.2
                    linarith only [hlam, p1267_0]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1297 | h1297
            · linarith only [h0, h1178, h1256, h1297, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1299 | h1299
              · linarith only [h0, h1179, h1256, h1297, h1299, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1301 | h1301
                · linarith only [h0, h1179, h1256, h1301, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi4]
                · rcases h1bigk with h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c | h1303c
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [hlam, p1303_0]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [h0, hlam, p1303_0]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [h0, h1256, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1303_1]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [h0, h1256, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1303_1]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [h1180, hlam, p1303_0]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [h1256, hc01, hc25, hlam, hphi, ht12, p1303_1]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [hlam, p1303_0]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [h1256, hc13, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1303_1]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [h1256, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p1303_1]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [h1256, hlam, p1303_0]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [h1178, hlam, p1303_0]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [h1254, hlam, p1303_1]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [hlam, p1303_0]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [h1297, hlam, p1303_1]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [h1299, hlam, p1303_1]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [h1179, hlam, p1303_0]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [h1255, hlam, p1303_1]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [h1179, h1254, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1303_1]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [hlam, p1303_0]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [h1301, hlam, p1303_1]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [hc01, hc15, hlam, hphi, p1303_1]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [h0, h1301, hc02, hc45, hlam, hphi, ht23, ht34, p1303_1]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [h1254, h1301, hc23, hc45, hlam, hphi, ht34, p1303_1]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [h1254, h1297, h1301, hc23, hc45, hlam, hphi, ht34, p1303_1]
                  · have p1303_0 := h1303c.1
                    have p1303_1 := h1303c.2.1
                    have p1303_2 := h1303c.2.2.1
                    have p1303_3 := h1303c.2.2.2
                    linarith only [hlam, p1303_0]
        · linarith only [h0, h1179, h1255, hlam]
      · linarith only [h0, h1178, h1254, hlam]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h1331 | h1331
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1332 | h1332
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1333 | h1333
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1334 | h1334
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1335 | h1335
            · linarith only [h1178, h1179, h1335, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1337 | h1337
              · linarith only [h1178, h1179, h1335, h1337, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1339 | h1339
                · rcases h1bigk with h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c | h1340c
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [hlam, p1340_0]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [h0, hlam, p1340_0]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [h1179, h1335, hc13, hc34, hlam, hphi, p1340_1]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [h1179, hlam, p1340_0]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [h1179, h1335, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1340_1, u5ehi1]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [hc01, hc12, hlam, hphi, p1340_1]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [hlam, p1340_0]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    rcases p1340_3 (m.d 0 1) (by simp) with h1348 | h1348
                    · linarith only [h0, h1348, hlam]
                    · linarith only [h1178, h1348, hlam]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [h1179, h1331, h1334, hc12, hlam, hphi, ht01, ht0b, ht5b, p1340_1, u5ehi2]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [h1334, hc12, hlam, hphi, ht01, ht0b, ht5b, p1340_1, u5ehi2]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [h1178, hlam, p1340_0]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [h1332, hlam, p1340_1]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [hlam, p1340_0]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [h1335, hlam, p1340_1]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [h1337, hlam, p1340_1]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [h1331, h1334, hc14, hlam, hphi, ht01, ht0b, ht5b, p1340_1, u5ehi2]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [h1333, hlam, p1340_1]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [h1332, h1335, hc23, hc34, hlam, hphi, p1340_1]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [hlam, p1340_0]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [h1334, h1335, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p1340_1, u5ehi2]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [h1331, hlam, p1340_0]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [h1334, hlam, p1340_1]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [h1331, h1332, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1340_1]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [h1339, hlam, p1340_0]
                  · have p1340_0 := h1340c.1
                    have p1340_1 := h1340c.2.1
                    have p1340_2 := h1340c.2.2.1
                    have p1340_3 := h1340c.2.2.2
                    linarith only [hlam, p1340_0]
                · linarith only [h1179, h1331, h1339, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi1]
          · linarith only [h0, h1331, h1334, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
        · linarith only [h0, h1331, h1333, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
      · linarith only [h0, h1331, h1332, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi1]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h1372 | h1372
      · rcases m.htr 1 2 4 (by decide) (by decide) with h1373 | h1373
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1374 | h1374
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1375 | h1375
            · linarith only [h1178, h1179, h1375, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1377 | h1377
              · linarith only [h1178, h1179, h1373, h1377, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1379 | h1379
                · rcases h1bigk with h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c | h1380c
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [hlam, p1380_0]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [h0, hlam, p1380_0]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [h1331, h1375, h1379, hc13, hc34, hlam, hphi, p1380_1]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [h1179, hlam, p1380_0]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [h1331, hlam, p1380_0]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [hc01, hc12, hlam, hphi, p1380_1]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [hlam, p1380_0]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    rcases p1380_3 (m.d 0 1) (by simp) with h1388 | h1388
                    · linarith only [h0, h1388, hlam]
                    · linarith only [h1178, h1388, hlam]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [h1379, hc12, hlam, hphi, ht01, ht0b, ht5b, p1380_1, u5ehi1]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [h1178, h1331, h1372, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1380_1]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [h1178, hlam, p1380_0]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [h1372, hlam, p1380_1]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [hlam, p1380_0]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [h1375, hlam, p1380_1]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [h1377, hlam, p1380_1]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [h1178, h1372, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1380_1]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [h1373, hlam, p1380_1]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [h1372, h1375, hc23, hc34, hlam, hphi, p1380_1]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [hlam, p1380_0]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [h1178, h1331, h1372, h1375, hc23, hc34, hlam, hphi, p1380_1]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [h1178, h1372, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1380_1]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [h1374, hlam, p1380_1]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [h1372, h1377, hc23, hc35, hlam, hphi, p1380_1]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [h1379, hlam, p1380_0]
                  · have p1380_0 := h1380c.1
                    have p1380_1 := h1380c.2.1
                    have p1380_2 := h1380c.2.2.1
                    have p1380_3 := h1380c.2.2.2
                    linarith only [hlam, p1380_0]
                · linarith only [h1178, h1179, h1372, h1379, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1409 | h1409
            · linarith only [h0, h1178, h1374, h1409, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1411 | h1411
              · linarith only [h1178, h1179, h1373, h1374, h1411, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1413 | h1413
                · linarith only [h1373, h1374, h1413, hlam]
                · linarith only [h1178, h1179, h1372, h1413, hc23, hc45, hlam, hphi, ht34]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h1416 | h1416
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1417 | h1417
            · linarith only [h0, h1178, h1373, h1417, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1419 | h1419
              · linarith only [h1178, h1331, h1373, h1416, h1419, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1421 | h1421
                · rcases h1bigk with h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c | h1422c
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [hlam, p1422_0]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h0, hlam, p1422_0]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h1331, h1372, h1373, h1416, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1422_1]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h1179, hlam, p1422_0]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h1331, hlam, p1422_0]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h1373, hc01, hc24, hlam, hphi, ht12, p1422_1]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [hlam, p1422_0]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h1372, h1373, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1422_1]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h1373, hlam, p1422_0]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h1373, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p1422_1, u5ehi1]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h1178, hlam, p1422_0]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h1372, hlam, p1422_1]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [hlam, p1422_0]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h1417, hlam, p1422_1]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h1419, hlam, p1422_1]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h1178, h1372, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1422_1]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h0, h1417, hc02, hc34, hlam, hphi, ht23, p1422_1]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h1372, h1417, hc23, hc34, hlam, hphi, p1422_1]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [hlam, p1422_0]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h1178, h1331, h1372, h1417, hc23, hc34, hlam, hphi, p1422_1]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h1178, h1372, h1373, h1416, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1422_1]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h1416, hlam, p1422_1]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h1372, h1373, h1416, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1422_1]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [h1421, hlam, p1422_0]
                  · have p1422_0 := h1422c.1
                    have p1422_1 := h1422c.2.1
                    have p1422_2 := h1422c.2.2.1
                    have p1422_3 := h1422c.2.2.2
                    linarith only [hlam, p1422_0]
                · linarith only [h1178, h1179, h1372, h1421, hc23, hc45, hlam, hphi, ht34]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h1449 | h1449
            · linarith only [h0, h1178, h1373, h1449, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h1451 | h1451
              · linarith only [h0, h1178, h1373, h1451, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h1453 | h1453
                · rcases h1bigk with h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c | h1454c
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [hlam, p1454_0]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h0, hlam, p1454_0]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h0, h1373, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1454_1]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h1179, hlam, p1454_0]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h1331, hlam, p1454_0]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h1373, hc01, hc24, hlam, hphi, ht12, p1454_1]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [hlam, p1454_0]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h1373, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p1454_1]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h1373, hlam, p1454_0]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h1416, hlam, p1454_0]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h1178, hlam, p1454_0]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h1372, hlam, p1454_1]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [hlam, p1454_0]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h1449, hlam, p1454_1]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h1451, hlam, p1454_1]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h1178, hc13, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1454_1]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h1449, hc12, hc34, hlam, hphi, ht23, p1454_1]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h1372, h1449, hc23, hc34, hlam, hphi, p1454_1]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [hlam, p1454_0]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h0, h1178, h1372, h1416, h1449, hc23, hc34, hlam, hphi, p1454_1]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h1178, h1372, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1454_1]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h0, h1178, h1372, h1451, hc23, hc35, hlam, hphi, p1454_1]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h1372, h1451, hc23, hc35, hlam, hphi, p1454_1]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [h1453, hlam, p1454_0]
                  · have p1454_0 := h1454c.1
                    have p1454_1 := h1454c.2.1
                    have p1454_2 := h1454c.2.2.1
                    have p1454_3 := h1454c.2.2.2
                    linarith only [hlam, p1454_0]
                · linarith only [h1178, h1179, h1372, h1453, hc23, hc45, hlam, hphi, ht34]
      · linarith only [h0, h1178, h1372, hlam]

end R2N4
