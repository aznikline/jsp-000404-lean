import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_7S12
import Jsp000404.R1LeavesN7_7S13

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6218000 in
set_option maxHeartbeats 6218000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s11_x1_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg6343 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h6418 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h8520 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
    (h8587 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  have h6343 := hg6343
  rcases m.htr 1 2 3 (by decide) (by decide) with h9064 | h9064
  · linarith only [h0, h4, h9064, hlam]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h9066 | h9066
    · linarith only [h0, h5543, h9066, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h9068 | h9068
      · linarith only [h2, h6343, h8587, h9066, h9068, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h9070 | h9070
        · linarith only [h1, h6418, h9070, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h9072 | h9072
          · linarith only [h1, h8520, h9072, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h9074 | h9074
            · linarith only [h2, h8587, h9074, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h9076 | h9076
              · rcases m.htr 2 3 5 (by decide) (by decide) with h9077 | h9077
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9078 | h9078
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9079 | h9079
                    · linarith only [h4, h6418, h8587, h9076, h9079, hc02, hc23, hlam, hphi]
                    · linarith only [h0, h4, h6418, h9078, h9079, hc12, hc24, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9082 | h9082
                    · linarith only [h0, h5543, h9078, h9082, hc12, hc34, hlam, hphi, ht23]
                    · rcases h1bigk with h9084c | h9084c | h9084c | h9084c | h9084c | h9084c | h9084c | h9084c | h9084c | h9084c | h9084c | h9084c | h9084c | h9084c | h9084c | h9084c | h9084c | h9084c | h9084c | h9084c | h9084c | h9084c | h9084c | h9084c | h9084c
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [hlam, p9084_0]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        rcases p9084_3 (m.d 0 1) (by simp) with h9086 | h9086
                        · rcases p9084_3 (m.d 1 2) (by simp) with h9087 | h9087
                          · linarith only [h9087, hlam, p9084_0]
                          · rcases p9084_3 (m.d 1 3) (by simp) with h9089 | h9089
                            · linarith only [h1, h9089, hlam]
                            · linarith only [h9064, h9089, hlam]
                        · linarith only [h9086, hlam, p9084_0]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        rcases p9084_3 (m.d 0 1) (by simp) with h9093 | h9093
                        · rcases p9084_3 (m.d 1 2) (by simp) with h9094 | h9094
                          · linarith only [h0, h9094, hlam]
                          · rcases p9084_3 (m.d 1 3) (by simp) with h9096 | h9096
                            · linarith only [h9096, hlam, p9084_0]
                            · rcases p9084_3 (m.d 1 4) (by simp) with h9098 | h9098
                              · linarith only [h2, h9098, hlam]
                              · linarith only [h9070, h9098, hlam]
                        · linarith only [h9093, hlam, p9084_0]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        rcases p9084_3 (m.d 0 1) (by simp) with h9102 | h9102
                        · rcases p9084_3 (m.d 1 2) (by simp) with h9103 | h9103
                          · linarith only [h0, h9103, hlam]
                          · rcases p9084_3 (m.d 1 3) (by simp) with h9105 | h9105
                            · linarith only [h1, h9105, hlam]
                            · rcases p9084_3 (m.d 1 4) (by simp) with h9107 | h9107
                              · linarith only [h9107, hlam, p9084_0]
                              · rcases p9084_3 (m.d 1 5) (by simp) with h9109 | h9109
                                · linarith only [h3, h9109, hlam]
                                · linarith only [h9074, h9109, hlam]
                        · linarith only [h9102, hlam, p9084_0]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        rcases p9084_3 (m.d 0 1) (by simp) with h9113 | h9113
                        · rcases p9084_3 (m.d 1 2) (by simp) with h9114 | h9114
                          · linarith only [h0, h9114, hlam]
                          · rcases p9084_3 (m.d 1 3) (by simp) with h9116 | h9116
                            · linarith only [h1, h9116, hlam]
                            · rcases p9084_3 (m.d 1 4) (by simp) with h9118 | h9118
                              · linarith only [h2, h9118, hlam]
                              · rcases p9084_3 (m.d 1 5) (by simp) with h9120 | h9120
                                · linarith only [h9120, hlam, p9084_0]
                                · rcases h1emax with h9122 | h9122 | h9122 | h9122 | h9122
                                  · linarith only [h9122, hlam, hphi, ht01, ht0b, ht5b, p9084_1, u5ehi1]
                                  · rcases h3bigk with h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c | h9124c
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [hlam, p9124_0]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [h6418, h9064, h9076, h9078, hc12, hc45, hlam, hphi, ht23, ht34, p9124_1]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [h4, hlam, p9124_1]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [h6418, hlam, p9124_0]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [h8520, hlam, p9124_0]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [h1, hlam, p9124_0]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [hlam, p9124_0]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [h9064, hlam, p9124_1]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [h9070, hlam, p9124_0]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [h9072, hlam, p9124_0]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      rcases p9124_3 (m.d 0 3) (by simp) with h9135 | h9135
                                      · linarith only [h4, h9135, hlam]
                                      · rcases p9124_3 (m.d 1 3) (by simp) with h9137 | h9137
                                        · linarith only [h9064, h9137, hlam]
                                        · rcases p9124_3 (m.d 2 3) (by simp) with h9139 | h9139
                                          · rcases p9124_3 (m.d 3 4) (by simp) with h9140 | h9140
                                            · linarith only [h9076, h9140, hlam]
                                            · linarith only [h6418, h9140, hlam]
                                          · linarith only [h4, h9139, hlam]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      rcases p9124_3 (m.d 0 3) (by simp) with h9144 | h9144
                                      · linarith only [h4, h9144, hlam]
                                      · linarith only [h1, h9144, hlam]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [hlam, p9124_0]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [h4, h6418, hc02, hc23, hlam, hphi, p9124_1]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [h0, h4, h6418, h9082, hc12, hc23, hlam, hphi, p9124_1]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [h0, h4, h9076, hc12, hc23, hlam, hphi, p9124_1]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [h9064, h9076, hc12, hc23, hlam, hphi, p9124_1]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [h9076, hlam, p9124_0]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [hlam, p9124_0]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [h9082, hlam, p9124_1]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [h0, h4, h9077, hc12, hc23, hlam, hphi, p9124_1]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [h9064, h9077, hc12, hc23, hlam, hphi, p9124_1]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [h9077, hlam, p9124_0]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [h0, h4, h6418, h9077, hc12, hc23, hlam, hphi, p9124_1]
                                    · have p9124_0 := h9124c.1
                                      have p9124_1 := h9124c.2.1
                                      have p9124_2 := h9124c.2.2.1
                                      have p9124_3 := h9124c.2.2.2
                                      linarith only [hlam, p9124_0]
                                  · rcases h3bigk with h9160c | h9160c | h9160c | h9160c | h9160c | h9160c | h9160c | h9160c | h9160c | h9160c | h9160c | h9160c | h9160c | h9160c | h9160c | h9160c | h9160c | h9160c | h9160c | h9160c | h9160c | h9160c | h9160c | h9160c | h9160c
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [hlam, p9160_0]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [h6418, h9064, hc12, hc34, hlam, hphi, ht23, p9160_1]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [h4, hlam, p9160_1]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [h6418, hlam, p9160_0]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [h8520, hlam, p9160_0]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [h1, hlam, p9160_0]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [hlam, p9160_0]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [h9064, hlam, p9160_1]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [h9070, hlam, p9160_0]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [h9072, hlam, p9160_0]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      rcases p9160_3 (m.d 0 3) (by simp) with h9171 | h9171
                                      · linarith only [h4, h9171, hlam]
                                      · rcases p9160_3 (m.d 1 3) (by simp) with h9173 | h9173
                                        · linarith only [h9064, h9173, hlam]
                                        · rcases p9160_3 (m.d 2 3) (by simp) with h9175 | h9175
                                          · rcases p9160_3 (m.d 3 4) (by simp) with h9176 | h9176
                                            · linarith only [h9076, h9176, hlam]
                                            · linarith only [h6418, h9176, hlam]
                                          · linarith only [h4, h9175, hlam]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      rcases p9160_3 (m.d 0 3) (by simp) with h9180 | h9180
                                      · linarith only [h4, h9180, hlam]
                                      · linarith only [h1, h9180, hlam]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [hlam, p9160_0]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [h1, h6418, h9064, hc12, hc23, hlam, hphi, p9160_1]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [h1, h8520, h9064, hc12, hc23, hlam, hphi, p9160_1]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [h1, h9064, h9076, hc12, hc23, hlam, hphi, p9160_1]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [h9064, h9076, hc12, hc23, hlam, hphi, p9160_1]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [h9076, hlam, p9160_0]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [hlam, p9160_0]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [h9082, hlam, p9160_1]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [h1, h9064, h9077, hc12, hc23, hlam, hphi, p9160_1]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [h9064, h9077, hc12, hc23, hlam, hphi, p9160_1]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [h9077, hlam, p9160_0]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [h1, h6418, h9064, h9077, hc12, hc23, hlam, hphi, p9160_1]
                                    · have p9160_0 := h9160c.1
                                      have p9160_1 := h9160c.2.1
                                      have p9160_2 := h9160c.2.2.1
                                      have p9160_3 := h9160c.2.2.2
                                      linarith only [hlam, p9160_0]
                                  · rcases h3bigk with h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c | h9196c
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [hlam, p9196_0]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [h6418, h9064, hc12, hc34, hlam, hphi, ht23, p9196_1]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [h4, hlam, p9196_1]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [h6418, hlam, p9196_0]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [h8520, hlam, p9196_0]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [h1, hlam, p9196_0]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [hlam, p9196_0]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [h9064, hlam, p9196_1]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [h9070, hlam, p9196_0]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [h9072, hlam, p9196_0]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      rcases p9196_3 (m.d 0 3) (by simp) with h9207 | h9207
                                      · linarith only [h4, h9207, hlam]
                                      · rcases p9196_3 (m.d 1 3) (by simp) with h9209 | h9209
                                        · linarith only [h9064, h9209, hlam]
                                        · rcases p9196_3 (m.d 2 3) (by simp) with h9211 | h9211
                                          · rcases p9196_3 (m.d 3 4) (by simp) with h9212 | h9212
                                            · linarith only [h9076, h9212, hlam]
                                            · linarith only [h6418, h9212, hlam]
                                          · linarith only [h4, h9211, hlam]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      rcases p9196_3 (m.d 0 3) (by simp) with h9216 | h9216
                                      · linarith only [h4, h9216, hlam]
                                      · linarith only [h1, h9216, hlam]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [hlam, p9196_0]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [h1, h6418, h9064, hc12, hc23, hlam, hphi, p9196_1]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [h1, h8520, h9064, hc12, hc23, hlam, hphi, p9196_1]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [h1, h9064, h9076, hc12, hc23, hlam, hphi, p9196_1]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [h9064, h9076, hc12, hc23, hlam, hphi, p9196_1]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [h9076, hlam, p9196_0]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [hlam, p9196_0]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [h9082, hlam, p9196_1]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [h1, h9064, h9077, hc12, hc23, hlam, hphi, p9196_1]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [h9064, h9077, hc12, hc23, hlam, hphi, p9196_1]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [h9077, hlam, p9196_0]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [h1, h6418, h9064, h9077, hc12, hc23, hlam, hphi, p9196_1]
                                    · have p9196_0 := h9196c.1
                                      have p9196_1 := h9196c.2.1
                                      have p9196_2 := h9196c.2.2.1
                                      have p9196_3 := h9196c.2.2.2
                                      linarith only [hlam, p9196_0]
                                  · rcases h3bigk with h9232c | h9232c | h9232c | h9232c | h9232c | h9232c | h9232c | h9232c | h9232c | h9232c | h9232c | h9232c | h9232c | h9232c | h9232c | h9232c | h9232c | h9232c | h9232c | h9232c | h9232c | h9232c | h9232c | h9232c | h9232c
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [hlam, p9232_0]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [h6418, h9064, hc12, hc34, hlam, hphi, ht23, p9232_1]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [h4, hlam, p9232_1]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [h6418, hlam, p9232_0]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [h8520, hlam, p9232_0]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [h1, hlam, p9232_0]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [hlam, p9232_0]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [h9064, hlam, p9232_1]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [h9070, hlam, p9232_0]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [h9072, hlam, p9232_0]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      rcases p9232_3 (m.d 0 3) (by simp) with h9243 | h9243
                                      · linarith only [h4, h9243, hlam]
                                      · rcases p9232_3 (m.d 1 3) (by simp) with h9245 | h9245
                                        · linarith only [h9064, h9245, hlam]
                                        · rcases p9232_3 (m.d 2 3) (by simp) with h9247 | h9247
                                          · rcases p9232_3 (m.d 3 4) (by simp) with h9248 | h9248
                                            · linarith only [h9076, h9248, hlam]
                                            · linarith only [h6418, h9248, hlam]
                                          · linarith only [h4, h9247, hlam]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      rcases p9232_3 (m.d 0 3) (by simp) with h9252 | h9252
                                      · linarith only [h4, h9252, hlam]
                                      · linarith only [h1, h9252, hlam]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [hlam, p9232_0]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [h1, h6418, h9064, hc12, hc23, hlam, hphi, p9232_1]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [h1, h8520, h9064, hc12, hc23, hlam, hphi, p9232_1]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [h1, h9064, h9076, hc12, hc23, hlam, hphi, p9232_1]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [h9064, h9076, hc12, hc23, hlam, hphi, p9232_1]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [h9076, hlam, p9232_0]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [hlam, p9232_0]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [h9082, hlam, p9232_1]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [h1, h9064, h9077, hc12, hc23, hlam, hphi, p9232_1]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [h9064, h9077, hc12, hc23, hlam, hphi, p9232_1]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [h9077, hlam, p9232_0]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [h1, h6418, h9064, h9077, hc12, hc23, hlam, hphi, p9232_1]
                                    · have p9232_0 := h9232c.1
                                      have p9232_1 := h9232c.2.1
                                      have p9232_2 := h9232c.2.2.1
                                      have p9232_3 := h9232c.2.2.2
                                      linarith only [hlam, p9232_0]
                        · linarith only [h9113, hlam, p9084_0]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [h0, hlam, p9084_0]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [hlam, p9084_0]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [h9064, hlam, p9084_0]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [h9066, hlam, p9084_0]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [h9068, hlam, p9084_0]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [h1, hlam, p9084_0]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [h1, h5543, h6418, h9078, hc12, hc45, hlam, hphi, ht23, ht34, p9084_1]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [hlam, p9084_0]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [h9070, hlam, p9084_1]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [h9072, hlam, p9084_1]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [h2, hlam, p9084_0]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [h2, h5543, h9078, hc12, hc45, hlam, hphi, ht23, ht34, p9084_1]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [h2, h5543, h9078, hc13, hc45, hlam, hphi, ht34, p9084_1]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [hlam, p9084_0]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [h9074, hlam, p9084_1]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [h3, hlam, p9084_0]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [h3, h8520, h9077, hc12, hc23, hlam, hphi, p9084_1]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [h3, h8520, h9064, h9077, hc12, hc23, hlam, hphi, p9084_1]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [h3, h8520, h9066, h9077, hc12, hc23, hlam, hphi, p9084_1]
                      · have p9084_0 := h9084c.1
                        have p9084_1 := h9084c.2.1
                        have p9084_2 := h9084c.2.2.1
                        have p9084_3 := h9084c.2.2.2
                        linarith only [hlam, p9084_0]
                · linarith only [h6418, h9076, h9077, hc03, hc35, hlam, hphi]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h9290 | h9290
                · linarith only [h8520, h9076, h9290, hc03, hc34, hlam, hphi]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9292 | h9292
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9293 | h9293
                    · rcases h1bigk with h9294c | h9294c | h9294c | h9294c | h9294c | h9294c | h9294c | h9294c | h9294c | h9294c | h9294c | h9294c | h9294c | h9294c | h9294c | h9294c | h9294c | h9294c | h9294c | h9294c | h9294c | h9294c | h9294c | h9294c | h9294c
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [hlam, p9294_0]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        rcases p9294_3 (m.d 0 1) (by simp) with h9296 | h9296
                        · rcases p9294_3 (m.d 1 2) (by simp) with h9297 | h9297
                          · linarith only [h9297, hlam, p9294_0]
                          · rcases p9294_3 (m.d 1 3) (by simp) with h9299 | h9299
                            · linarith only [h1, h9299, hlam]
                            · linarith only [h9064, h9299, hlam]
                        · linarith only [h9296, hlam, p9294_0]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        rcases p9294_3 (m.d 0 1) (by simp) with h9303 | h9303
                        · rcases p9294_3 (m.d 1 2) (by simp) with h9304 | h9304
                          · linarith only [h0, h9304, hlam]
                          · rcases p9294_3 (m.d 1 3) (by simp) with h9306 | h9306
                            · linarith only [h9306, hlam, p9294_0]
                            · rcases p9294_3 (m.d 1 4) (by simp) with h9308 | h9308
                              · linarith only [h2, h9308, hlam]
                              · linarith only [h9070, h9308, hlam]
                        · linarith only [h9303, hlam, p9294_0]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        rcases p9294_3 (m.d 0 1) (by simp) with h9312 | h9312
                        · rcases p9294_3 (m.d 1 2) (by simp) with h9313 | h9313
                          · linarith only [h0, h9313, hlam]
                          · rcases p9294_3 (m.d 1 3) (by simp) with h9315 | h9315
                            · linarith only [h1, h9315, hlam]
                            · rcases p9294_3 (m.d 1 4) (by simp) with h9317 | h9317
                              · linarith only [h9317, hlam, p9294_0]
                              · rcases p9294_3 (m.d 1 5) (by simp) with h9319 | h9319
                                · linarith only [h3, h9319, hlam]
                                · linarith only [h9074, h9319, hlam]
                        · linarith only [h9312, hlam, p9294_0]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        rcases p9294_3 (m.d 0 1) (by simp) with h9323 | h9323
                        · rcases p9294_3 (m.d 1 2) (by simp) with h9324 | h9324
                          · linarith only [h0, h9324, hlam]
                          · rcases p9294_3 (m.d 1 3) (by simp) with h9326 | h9326
                            · linarith only [h1, h9326, hlam]
                            · rcases p9294_3 (m.d 1 4) (by simp) with h9328 | h9328
                              · linarith only [h2, h9328, hlam]
                              · rcases p9294_3 (m.d 1 5) (by simp) with h9330 | h9330
                                · linarith only [h9330, hlam, p9294_0]
                                · rcases h1emax with h9332 | h9332 | h9332 | h9332 | h9332
                                  · linarith only [h9332, hlam, hphi, ht01, ht0b, ht5b, p9294_1, u5ehi1]
                                  · rcases h3bigk with h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c | h9334c
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [hlam, p9334_0]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [h4, h9064, h9290, h9293, hc12, hc34, hlam, hphi, ht23, p9334_1]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [h4, hlam, p9334_1]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [h6418, hlam, p9334_0]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [h8520, hlam, p9334_0]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [h1, hlam, p9334_0]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [hlam, p9334_0]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [h9064, hlam, p9334_1]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [h9070, hlam, p9334_0]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [h9072, hlam, p9334_0]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [h9290, h9293, hc03, hc34, hlam, hphi, p9334_1]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [h9064, h9290, h9293, hc12, hc34, hlam, hphi, ht23, p9334_1]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [hlam, p9334_0]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [h9076, hlam, p9334_0]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [h9290, hlam, p9334_0]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      rcases p9334_3 (m.d 0 3) (by simp) with h9350 | h9350
                                      · linarith only [h9350, hlam, p9334_0]
                                      · rcases p9334_3 (m.d 1 3) (by simp) with h9352 | h9352
                                        · linarith only [h9070, h9352, hlam]
                                        · rcases p9334_3 (m.d 2 3) (by simp) with h9354 | h9354
                                          · linarith only [h9076, h9354, hlam]
                                          · linarith only [h4, h9354, hlam]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      rcases p9334_3 (m.d 0 3) (by simp) with h9357 | h9357
                                      · linarith only [h6418, h9357, hlam]
                                      · linarith only [h1, h9357, hlam]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p9334_1]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [hlam, p9334_0]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [h1, h8520, h9064, hc12, hc34, hlam, hphi, ht23, p9334_1]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      rcases p9334_3 (m.d 0 3) (by simp) with h9363 | h9363
                                      · linarith only [h9363, hlam, p9334_0]
                                      · rcases p9334_3 (m.d 1 3) (by simp) with h9365 | h9365
                                        · linarith only [h9072, h9365, hlam]
                                        · rcases p9334_3 (m.d 2 3) (by simp) with h9367 | h9367
                                          · linarith only [h9290, h9367, hlam]
                                          · linarith only [h4, h9367, hlam]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      rcases p9334_3 (m.d 0 3) (by simp) with h9370 | h9370
                                      · linarith only [h8520, h9370, hlam]
                                      · linarith only [h1, h9370, hlam]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p9334_1]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [h9293, hlam, p9334_0]
                                    · have p9334_0 := h9334c.1
                                      have p9334_1 := h9334c.2.1
                                      have p9334_2 := h9334c.2.2.1
                                      have p9334_3 := h9334c.2.2.2
                                      linarith only [hlam, p9334_0]
                                  · rcases h3bigk with h9376c | h9376c | h9376c | h9376c | h9376c | h9376c | h9376c | h9376c | h9376c | h9376c | h9376c | h9376c | h9376c | h9376c | h9376c | h9376c | h9376c | h9376c | h9376c | h9376c | h9376c | h9376c | h9376c | h9376c | h9376c
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [hlam, p9376_0]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [h6418, h9064, hc12, hc34, hlam, hphi, ht23, p9376_1]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [h4, hlam, p9376_1]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [h6418, hlam, p9376_0]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [h8520, hlam, p9376_0]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [h1, hlam, p9376_0]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [hlam, p9376_0]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [h9064, hlam, p9376_1]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [h9070, hlam, p9376_0]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [h9072, hlam, p9376_0]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [h9076, hc03, hc34, hlam, hphi, p9376_1]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [h9064, h9076, hc12, hc34, hlam, hphi, ht23, p9376_1]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [hlam, p9376_0]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [h9076, hlam, p9376_0]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [h9290, hlam, p9376_0]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      rcases p9376_3 (m.d 0 3) (by simp) with h9392 | h9392
                                      · linarith only [h9392, hlam, p9376_0]
                                      · rcases p9376_3 (m.d 1 3) (by simp) with h9394 | h9394
                                        · linarith only [h9070, h9394, hlam]
                                        · rcases p9376_3 (m.d 2 3) (by simp) with h9396 | h9396
                                          · linarith only [h9076, h9396, hlam]
                                          · linarith only [h4, h9396, hlam]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      rcases p9376_3 (m.d 0 3) (by simp) with h9399 | h9399
                                      · linarith only [h6418, h9399, hlam]
                                      · linarith only [h1, h9399, hlam]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p9376_1]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [hlam, p9376_0]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [h1, h8520, h9064, hc12, hc34, hlam, hphi, ht23, p9376_1]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      rcases p9376_3 (m.d 0 3) (by simp) with h9405 | h9405
                                      · linarith only [h9405, hlam, p9376_0]
                                      · rcases p9376_3 (m.d 1 3) (by simp) with h9407 | h9407
                                        · linarith only [h9072, h9407, hlam]
                                        · rcases p9376_3 (m.d 2 3) (by simp) with h9409 | h9409
                                          · linarith only [h9290, h9409, hlam]
                                          · linarith only [h4, h9409, hlam]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      rcases p9376_3 (m.d 0 3) (by simp) with h9412 | h9412
                                      · linarith only [h8520, h9412, hlam]
                                      · linarith only [h1, h9412, hlam]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p9376_1]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [h9293, hlam, p9376_0]
                                    · have p9376_0 := h9376c.1
                                      have p9376_1 := h9376c.2.1
                                      have p9376_2 := h9376c.2.2.1
                                      have p9376_3 := h9376c.2.2.2
                                      linarith only [hlam, p9376_0]
                                  · rcases h3bigk with h9418c | h9418c | h9418c | h9418c | h9418c | h9418c | h9418c | h9418c | h9418c | h9418c | h9418c | h9418c | h9418c | h9418c | h9418c | h9418c | h9418c | h9418c | h9418c | h9418c | h9418c | h9418c | h9418c | h9418c | h9418c
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [hlam, p9418_0]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [h6418, h9064, hc12, hc34, hlam, hphi, ht23, p9418_1]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [h4, hlam, p9418_1]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [h6418, hlam, p9418_0]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [h8520, hlam, p9418_0]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [h1, hlam, p9418_0]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [hlam, p9418_0]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [h9064, hlam, p9418_1]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [h9070, hlam, p9418_0]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [h9072, hlam, p9418_0]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [h9076, hc03, hc34, hlam, hphi, p9418_1]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [h9064, h9076, hc12, hc34, hlam, hphi, ht23, p9418_1]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [hlam, p9418_0]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [h9076, hlam, p9418_0]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [h9290, hlam, p9418_0]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      rcases p9418_3 (m.d 0 3) (by simp) with h9434 | h9434
                                      · linarith only [h9434, hlam, p9418_0]
                                      · rcases p9418_3 (m.d 1 3) (by simp) with h9436 | h9436
                                        · linarith only [h9070, h9436, hlam]
                                        · rcases p9418_3 (m.d 2 3) (by simp) with h9438 | h9438
                                          · linarith only [h9076, h9438, hlam]
                                          · linarith only [h4, h9438, hlam]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      rcases p9418_3 (m.d 0 3) (by simp) with h9441 | h9441
                                      · linarith only [h6418, h9441, hlam]
                                      · linarith only [h1, h9441, hlam]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p9418_1]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [hlam, p9418_0]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [h1, h8520, h9064, hc12, hc34, hlam, hphi, ht23, p9418_1]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      rcases p9418_3 (m.d 0 3) (by simp) with h9447 | h9447
                                      · linarith only [h9447, hlam, p9418_0]
                                      · rcases p9418_3 (m.d 1 3) (by simp) with h9449 | h9449
                                        · linarith only [h9072, h9449, hlam]
                                        · rcases p9418_3 (m.d 2 3) (by simp) with h9451 | h9451
                                          · linarith only [h9290, h9451, hlam]
                                          · linarith only [h4, h9451, hlam]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      rcases p9418_3 (m.d 0 3) (by simp) with h9454 | h9454
                                      · linarith only [h8520, h9454, hlam]
                                      · linarith only [h1, h9454, hlam]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p9418_1]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [h9293, hlam, p9418_0]
                                    · have p9418_0 := h9418c.1
                                      have p9418_1 := h9418c.2.1
                                      have p9418_2 := h9418c.2.2.1
                                      have p9418_3 := h9418c.2.2.2
                                      linarith only [hlam, p9418_0]
                                  · rcases h3bigk with h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c | h9460c
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [hlam, p9460_0]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [h6418, h9064, hc12, hc34, hlam, hphi, ht23, p9460_1]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [h4, hlam, p9460_1]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [h6418, hlam, p9460_0]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [h8520, hlam, p9460_0]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [h1, hlam, p9460_0]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [hlam, p9460_0]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [h9064, hlam, p9460_1]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [h9070, hlam, p9460_0]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [h9072, hlam, p9460_0]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [h9076, hc03, hc34, hlam, hphi, p9460_1]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [h9064, h9076, hc12, hc34, hlam, hphi, ht23, p9460_1]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [hlam, p9460_0]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [h9076, hlam, p9460_0]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [h9290, hlam, p9460_0]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      rcases p9460_3 (m.d 0 3) (by simp) with h9476 | h9476
                                      · linarith only [h9476, hlam, p9460_0]
                                      · rcases p9460_3 (m.d 1 3) (by simp) with h9478 | h9478
                                        · linarith only [h9070, h9478, hlam]
                                        · rcases p9460_3 (m.d 2 3) (by simp) with h9480 | h9480
                                          · linarith only [h9076, h9480, hlam]
                                          · linarith only [h4, h9480, hlam]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      rcases p9460_3 (m.d 0 3) (by simp) with h9483 | h9483
                                      · linarith only [h6418, h9483, hlam]
                                      · linarith only [h1, h9483, hlam]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [h0, h4, hc12, hc34, hlam, hphi, ht23, p9460_1]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [hlam, p9460_0]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [h1, h8520, h9064, hc12, hc34, hlam, hphi, ht23, p9460_1]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      rcases p9460_3 (m.d 0 3) (by simp) with h9489 | h9489
                                      · linarith only [h9489, hlam, p9460_0]
                                      · rcases p9460_3 (m.d 1 3) (by simp) with h9491 | h9491
                                        · linarith only [h9072, h9491, hlam]
                                        · rcases p9460_3 (m.d 2 3) (by simp) with h9493 | h9493
                                          · linarith only [h9290, h9493, hlam]
                                          · linarith only [h4, h9493, hlam]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      rcases p9460_3 (m.d 0 3) (by simp) with h9496 | h9496
                                      · linarith only [h8520, h9496, hlam]
                                      · linarith only [h1, h9496, hlam]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [h0, h4, hc12, hc35, hlam, hphi, ht23, p9460_1]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [h9293, hlam, p9460_0]
                                    · have p9460_0 := h9460c.1
                                      have p9460_1 := h9460c.2.1
                                      have p9460_2 := h9460c.2.2.1
                                      have p9460_3 := h9460c.2.2.2
                                      linarith only [hlam, p9460_0]
                        · linarith only [h9323, hlam, p9294_0]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [h0, hlam, p9294_0]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [hlam, p9294_0]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [h9064, hlam, p9294_0]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [h9066, hlam, p9294_0]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [h9068, hlam, p9294_0]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [h1, hlam, p9294_0]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [h2, h8587, h9070, h9076, h9292, hc12, hc34, hlam, hphi, ht23, p9294_1]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [hlam, p9294_0]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [h9070, hlam, p9294_1]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [h9072, hlam, p9294_1]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [h2, hlam, p9294_0]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [h2, h8587, h9076, h9292, hc12, hc34, hlam, hphi, ht23, p9294_1]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [h2, h8587, h9076, h9292, hc13, hc34, hlam, hphi, p9294_1]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [hlam, p9294_0]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [h9074, hlam, p9294_1]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [h3, hlam, p9294_0]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [h3, h8587, h9076, h9292, hc12, hc34, hlam, hphi, ht23, p9294_1]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [h3, h8587, h9064, h9076, h9292, hc12, hc34, hlam, hphi, ht23, p9294_1]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [h3, h8587, h9066, h9076, h9292, hc12, hc34, hlam, hphi, ht23, p9294_1]
                      · have p9294_0 := h9294c.1
                        have p9294_1 := h9294c.2.1
                        have p9294_2 := h9294c.2.2.1
                        have p9294_3 := h9294c.2.2.2
                        linarith only [hlam, p9294_0]
                    · linarith only [h9076, h9292, h9293, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9524 | h9524
                    · linarith only [h0, h4, h9076, h9292, h9524, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h0, h4, h9076, h9524, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6218000 in
set_option maxHeartbeats 6218000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s11_x1_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg6343 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h6418 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h8520 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  have h6343 := hg6343
  rcases m.htr 0 4 5 (by decide) (by decide) with h8587 | h8587
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s11_x1_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5543 hg6343 h6418 h8520 h8587
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s11_x1_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5543 hg6343 h6418 h8520 h8587

set_option maxHeartbeats 6218000 in
set_option maxHeartbeats 6218000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s11_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg6343 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h6418 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  have h6343 := hg6343
  rcases m.htr 0 3 5 (by decide) (by decide) with h8520 | h8520
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s11_x1_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5543 hg6343 h6418 h8520
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s11_x1_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5543 hg6343 h6418 h8520

set_option maxHeartbeats 6218000 in
set_option maxHeartbeats 6218000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s11 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg6343 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  have h6343 := hg6343
  rcases m.htr 0 3 4 (by decide) (by decide) with h6418 | h6418
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s11_x0 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5543 hg6343 h6418
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s11_x1 m hb1 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg5543 hg6343 h6418

set_option maxHeartbeats 6368000 in
set_option maxHeartbeats 6368000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s10 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg5543 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h1bigk := hb1.1
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h5543 := hg5543
  rcases m.htr 0 2 5 (by decide) (by decide) with h6343 | h6343
  · rcases m.htr 0 3 4 (by decide) (by decide) with h6344 | h6344
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6345 | h6345
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6346 | h6346
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6347 | h6347
          · linarith only [h4, h6343, h6347, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6349 | h6349
            · linarith only [h5543, h6343, h6349, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6351 | h6351
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6352 | h6352
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6353 | h6353
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6354 | h6354
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6355 | h6355
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h6356 | h6356
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h6357 | h6357
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h6358 | h6358
                            · linarith only [h1, h6352, h6358, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                            · rcases h1bigk with h6360c | h6360c | h6360c | h6360c | h6360c | h6360c | h6360c | h6360c | h6360c | h6360c | h6360c | h6360c | h6360c | h6360c | h6360c | h6360c | h6360c | h6360c | h6360c | h6360c | h6360c | h6360c | h6360c | h6360c | h6360c
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [hlam, p6360_0]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [h6351, h6357, h6358, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6360_1]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [h6347, h6351, h6357, h6358, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6360_1]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [h6349, h6351, h6357, h6358, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6360_1]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                rcases p6360_3 (m.d 0 1) (by simp) with h6365 | h6365
                                · rcases p6360_3 (m.d 1 2) (by simp) with h6366 | h6366
                                  · linarith only [h0, h6366, hlam]
                                  · linarith only [h6351, h6366, hlam]
                                · linarith only [h6365, hlam, p6360_0]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [h0, hlam, p6360_0]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [hlam, p6360_0]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [h6347, hlam, p6360_0]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [h6349, hlam, p6360_0]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [h0, h5543, h6351, h6355, h6357, h6358, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6360_1]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [h1, hlam, p6360_0]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [h1, h6351, h6357, h6358, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6360_1]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [hlam, p6360_0]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [h1, h6349, h6351, h6357, h6358, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6360_1]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [h1, h6351, h6357, h6358, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6360_1]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [h2, hlam, p6360_0]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [h6351, h6357, h6358, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6360_1]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [h6352, hlam, p6360_0]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [hlam, p6360_0]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [h2, h6351, h6357, h6358, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6360_1]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [h3, hlam, p6360_0]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [h6351, hlam, p6360_1]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [h6353, hlam, p6360_0]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [h6354, hlam, p6360_0]
                              · have p6360_0 := h6360c.1
                                have p6360_1 := h6360c.2.1
                                have p6360_2 := h6360c.2.2.1
                                have p6360_3 := h6360c.2.2.2
                                linarith only [hlam, p6360_0]
                          · linarith only [h0, h5543, h6351, h6356, h6357, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                        · linarith only [h0, h4, h6351, h6356, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                      · linarith only [h0, h4, h6351, h6355, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h4, h6343, h6346, h6349, h6351, h6354, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                  · linarith only [h4, h6343, h6345, h6347, h6351, h6353, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                · linarith only [h4, h6344, h6347, h6351, h6352, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
              · linarith only [h4, h6343, h6351, hc12, hc23, hlam, hphi]
        · linarith only [h5543, h6343, h6346, hlam]
      · linarith only [h4, h6343, h6345, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6399 | h6399
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6400 | h6400
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6401 | h6401
          · linarith only [h0, h4, h6401, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h6403 | h6403
            · linarith only [h5543, h6343, h6403, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h6405 | h6405
              · rcases m.htr 1 3 4 (by decide) (by decide) with h6406 | h6406
                · linarith only [h1, h6344, h6406, hlam]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h6408 | h6408
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h6409 | h6409
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h6410 | h6410
                      · linarith only [h0, h4, h6344, h6405, h6410, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi2]
                      · linarith only [h0, h4, h6405, h6410, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, u5ehi2]
                    · linarith only [h6400, h6403, h6405, h6409, hc04, hlam, hphi, ht0b, ht5b, u5ehi2]
                  · linarith only [h6344, h6399, h6408, hc13, hc34, hlam, hphi]
              · linarith only [h4, h6343, h6344, h6405, hc12, hc34, hlam, hphi, ht23]
        · linarith only [h4, h6343, h6344, h6400, hlam]
      · linarith only [h4, h6343, h6399, hlam]
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s11 m hb1 hb3 hb5 h0 h1 h2 h3 h4 h5543 h6343

end R2N4
