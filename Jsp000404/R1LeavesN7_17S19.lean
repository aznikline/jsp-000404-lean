import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_17S10
import Jsp000404.R1LeavesN7_17S17
import Jsp000404.R1LeavesN7_17S18

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9764000 in
set_option maxHeartbeats 9764000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s7_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6421 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h6422 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h7022 | h7022
  · rcases m.htr 0 2 3 (by decide) (by decide) with h7023 | h7023
    · rcases m.htr 0 2 4 (by decide) (by decide) with h7024 | h7024
      · rcases m.htr 0 2 5 (by decide) (by decide) with h7025 | h7025
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7026 | h7026
          · linarith only [h6421, h6422, h7026, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7028 | h7028
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7029 | h7029
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7030 | h7030
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7031 | h7031
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7032 | h7032
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7033 | h7033
                      · linarith only [h6421, h6422, h7026, h7028, h7031, h7033, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7035 | h7035
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7036 | h7036
                          · linarith only [h6421, h6422, h7030, h7033, h7036, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7038 | h7038
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7039 | h7039
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7040 | h7040
                                · rcases h0bigk with h7041c | h7041c | h7041c | h7041c | h7041c | h7041c | h7041c | h7041c | h7041c | h7041c | h7041c | h7041c | h7041c | h7041c | h7041c | h7041c | h7041c | h7041c | h7041c | h7041c | h7041c | h7041c | h7041c | h7041c | h7041c
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [hlam, p7041_0]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [h0, hlam, p7041_1]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [h6422, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7041_1]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [h6422, hlam, p7041_1]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [h6422, h7033, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7041_1]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [h6421, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p7041_1]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [hlam, p7041_0]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [h0, h6421, h7030, h7038, h7040, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7041_1]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [h0, h6421, h6422, h7030, h7038, h7040, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p7041_1]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    rcases p7041_3 (m.d 0 1) (by simp) with h7051 | h7051
                                    · linarith only [h0, h7051, hlam]
                                    · linarith only [h7022, h7051, hlam]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [h6421, hlam, p7041_1]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [h7023, hlam, p7041_1]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [hlam, p7041_0]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [h7026, hlam, p7041_1]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [h6421, h6422, h7022, h7032, h7038, h7040, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p7041_1]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [h6421, h7030, h7038, h7040, hc04, hc45, hlam, hphi, ht0b, ht5b, p7041_1]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [h7024, hlam, p7041_0]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [h6422, h7033, hc03, hc34, hlam, hphi, p7041_1]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [hlam, p7041_0]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    rcases p7041_3 (m.d 0 1) (by simp) with h7063 | h7063
                                    · linarith only [h6422, h7063, hlam]
                                    · linarith only [h7022, h7063, hlam]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [h7022, hlam, p7041_0]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [h7025, hlam, p7041_1]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [h7028, hlam, p7041_0]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [h7029, hlam, p7041_1]
                                  · have p7041_0 := h7041c.1
                                    have p7041_1 := h7041c.2.1
                                    have p7041_2 := h7041c.2.2.1
                                    have p7041_3 := h7041c.2.2.2
                                    linarith only [hlam, p7041_0]
                                · linarith only [h6421, h6422, h7033, h7040, hc13, hc45, hlam, hphi, ht34]
                              · linarith only [h6422, h7022, h7033, h7035, h7036, h7038, h7039, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h6421, h6422, h7028, h7033, h7038, hc23, hc34, hlam, hphi]
                        · linarith only [h6421, h6422, h7035, hc13, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h7025, h7032, hlam]
                  · linarith only [h0, h7024, h7031, hlam]
                · linarith only [h0, h7023, h7030, hlam]
              · linarith only [h6422, h7022, h7029, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7079 | h7079
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7080 | h7080
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7081 | h7081
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7082 | h7082
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7083 | h7083
                      · linarith only [h6421, h6422, h7026, h7083, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7085 | h7085
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7086 | h7086
                          · linarith only [h6421, h6422, h7080, h7083, h7086, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7088 | h7088
                            · linarith only [h6421, h7028, h7080, h7088, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7090 | h7090
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7091 | h7091
                                · rcases h0bigk with h7092c | h7092c | h7092c | h7092c | h7092c | h7092c | h7092c | h7092c | h7092c | h7092c | h7092c | h7092c | h7092c | h7092c | h7092c | h7092c | h7092c | h7092c | h7092c | h7092c | h7092c | h7092c | h7092c | h7092c | h7092c
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [hlam, p7092_0]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [h0, hlam, p7092_1]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [h6422, h7083, hc03, hc34, hlam, hphi, p7092_1]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [h6422, hlam, p7092_1]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [h6422, h7083, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p7092_1]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p7092_1]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [hlam, p7092_0]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    rcases p7092_3 (m.d 0 1) (by simp) with h7100 | h7100
                                    · linarith only [h0, h7100, hlam]
                                    · linarith only [h6421, h7100, hlam]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [h0, h6422, h7022, h7082, h7088, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7092_1]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    rcases p7092_3 (m.d 0 1) (by simp) with h7104 | h7104
                                    · linarith only [h0, h7104, hlam]
                                    · linarith only [h7022, h7104, hlam]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [h6421, hlam, p7092_1]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [h7023, hlam, p7092_1]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [hlam, p7092_0]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [h7026, hlam, p7092_1]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [h7028, hlam, p7092_1]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [h7022, h7082, h7088, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7092_1]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [h7024, hlam, p7092_0]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [h6421, h6422, h7080, h7083, hc23, hc34, hlam, hphi, p7092_1]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [hlam, p7092_0]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [h6422, h7022, h7082, h7083, h7088, hc23, hc34, hlam, hphi, p7092_1]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [h7022, hlam, p7092_0]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [h7025, hlam, p7092_1]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [h0, h6421, h7022, h7080, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7092_1]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [h7079, hlam, p7092_1]
                                  · have p7092_0 := h7092c.1
                                    have p7092_1 := h7092c.2.1
                                    have p7092_2 := h7092c.2.2.1
                                    have p7092_3 := h7092c.2.2.2
                                    linarith only [hlam, p7092_0]
                                · linarith only [h6421, h6422, h7080, h7083, h7091, hc23, hc45, hlam, hphi, ht34]
                              · linarith only [h6422, h7022, h7083, h7085, h7086, h7090, hc23, hc34, hlam, hphi]
                        · linarith only [h6421, h6422, h7085, hc13, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h7025, h7082, hlam]
                  · linarith only [h0, h7024, h7081, hlam]
                · linarith only [h0, h6421, h7023, h7080, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h6422, h7022, h7079, hlam]
        · linarith only [h0, h7022, h7025, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h7130 | h7130
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7131 | h7131
          · linarith only [h0, h6421, h7024, h7131, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7133 | h7133
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7134 | h7134
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7135 | h7135
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7136 | h7136
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7137 | h7137
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7138 | h7138
                      · linarith only [h0, h6421, h7024, h7131, h7136, h7138, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7140 | h7140
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7141 | h7141
                          · linarith only [h0, h6421, h7024, h7135, h7136, h7138, h7141, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7143 | h7143
                            · linarith only [h0, h6421, h7024, h7135, h7136, h7143, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h0, h6421, h7024, h7133, h7136, h7143, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h6421, h7024, h7136, h7140, hc13, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h7024, h7136, h7137, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7148 | h7148
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7149 | h7149
                      · linarith only [h0, h6421, h7024, h7131, h7136, h7149, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7151 | h7151
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7152 | h7152
                          · linarith only [h0, h6421, h7135, h7136, h7149, h7152, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h0, h6421, h7135, h7136, h7152, hc23, hc34, hlam, hphi]
                        · linarith only [h0, h6421, h7135, h7136, h7151, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6421, h7130, h7135, h7148, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h6421, h7023, h7135, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h6421, h7024, h7133, h7134, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7159 | h7159
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7160 | h7160
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7161 | h7161
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7162 | h7162
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7163 | h7163
                      · linarith only [h0, h6421, h7131, h7163, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7165 | h7165
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7166 | h7166
                          · linarith only [h0, h6421, h7024, h7160, h7161, h7163, h7166, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7168 | h7168
                            · linarith only [h6421, h7133, h7160, h7168, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7170 | h7170
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7171 | h7171
                                · rcases h0bigk with h7172c | h7172c | h7172c | h7172c | h7172c | h7172c | h7172c | h7172c | h7172c | h7172c | h7172c | h7172c | h7172c | h7172c | h7172c | h7172c | h7172c | h7172c | h7172c | h7172c | h7172c | h7172c | h7172c | h7172c | h7172c
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [hlam, p7172_0]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h0, hlam, p7172_1]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h0, h7024, h7161, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7172_1]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h6422, hlam, p7172_1]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h0, h7024, h7161, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7172_1]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h7024, h7161, hc01, hc12, hlam, hphi, p7172_1]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [hlam, p7172_0]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h6421, h7024, h7161, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7172_1]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h7024, hlam, p7172_1]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h7022, h7024, h7161, h7162, h7168, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7172_1]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h6421, hlam, p7172_1]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h7023, hlam, p7172_1]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [hlam, p7172_0]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h7131, hlam, p7172_1]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h7133, hlam, p7172_1]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h7022, h7024, h7161, h7162, h7168, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7172_1]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h7024, h7161, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7172_1]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h6421, h7024, h7161, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7172_1]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [hlam, p7172_0]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h7022, h7024, h7161, h7162, h7168, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7172_1]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h7022, hlam, p7172_0]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h7130, hlam, p7172_1]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h0, h6421, h7022, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7172_1]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [h7159, hlam, p7172_1]
                                  · have p7172_0 := h7172c.1
                                    have p7172_1 := h7172c.2.1
                                    have p7172_2 := h7172c.2.2.1
                                    have p7172_3 := h7172c.2.2.2
                                    linarith only [hlam, p7172_0]
                                · linarith only [h6421, h6422, h7160, h7163, h7171, hc23, hc45, hlam, hphi, ht34]
                              · linarith only [h0, h7022, h7024, h7165, h7170, hlam]
                        · linarith only [h0, h6421, h7024, h7160, h7161, h7165, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h7024, h7130, h7162, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7202 | h7202
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7203 | h7203
                      · linarith only [h0, h6421, h7131, h7161, h7203, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7205 | h7205
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7206 | h7206
                          · linarith only [h0, h6421, h7160, h7161, h7203, h7206, hlam]
                          · linarith only [h0, h6421, h7160, h7161, h7206, hc23, hc34, hlam, hphi]
                        · linarith only [h0, h6421, h7160, h7161, h7205, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6421, h7130, h7160, h7202, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h6421, h7023, h7133, h7160, hc13, hc35, hlam, hphi]
              · linarith only [h0, h7022, h7024, h7159, hlam]
        · linarith only [h0, h7022, h7130, hlam]
    · linarith only [h0, h6421, h7023, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h7215 | h7215
    · rcases m.htr 0 2 4 (by decide) (by decide) with h7216 | h7216
      · rcases m.htr 0 2 5 (by decide) (by decide) with h7217 | h7217
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7218 | h7218
          · linarith only [h6421, h6422, h7218, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7220 | h7220
            · linarith only [h6421, h7022, h7220, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7222 | h7222
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7223 | h7223
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7224 | h7224
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7225 | h7225
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7226 | h7226
                      · linarith only [h6421, h6422, h7218, h7224, h7226, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7228 | h7228
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7229 | h7229
                          · linarith only [h6421, h7022, h7223, h7226, h7228, h7229, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7231 | h7231
                            · linarith only [h6421, h7022, h7220, h7223, h7231, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7233 | h7233
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7234 | h7234
                                · rcases h0bigk with h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c | h7235c
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [hlam, p7235_0]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [h0, hlam, p7235_1]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [h7022, h7226, h7228, hc03, hc34, hlam, hphi, p7235_1]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [h6422, hlam, p7235_1]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [h7022, hlam, p7235_1]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p7235_1]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [hlam, p7235_0]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    rcases p7235_3 (m.d 0 1) (by simp) with h7243 | h7243
                                    · linarith only [h0, h7243, hlam]
                                    · linarith only [h6421, h7243, hlam]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [h0, h6421, h6422, h7223, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7235_1]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [h0, h6421, h7022, h7223, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7235_1]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [h6421, hlam, p7235_1]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [h7215, hlam, p7235_1]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [hlam, p7235_0]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [h7218, hlam, p7235_1]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [h7220, hlam, p7235_1]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [h6421, h7223, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7235_1]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [h7216, hlam, p7235_0]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [h6421, h6422, h7223, h7226, hc23, hc34, hlam, hphi, p7235_1]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [hlam, p7235_0]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [h6421, h6422, h7022, h7223, h7226, hc23, hc34, hlam, hphi, p7235_1]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [h6421, h7223, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7235_1]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [h7217, hlam, p7235_1]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [h6421, h7220, h7223, hc23, hc35, hlam, hphi, p7235_1]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [h7222, hlam, p7235_1]
                                  · have p7235_0 := h7235c.1
                                    have p7235_1 := h7235c.2.1
                                    have p7235_2 := h7235c.2.2.1
                                    have p7235_3 := h7235c.2.2.2
                                    linarith only [hlam, p7235_0]
                                · linarith only [h0, h6421, h6422, h7216, h7223, h7226, h7233, h7234, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7264 | h7264
                                · rcases h0bigk with h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c | h7265c
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [hlam, p7265_0]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [h0, hlam, p7265_1]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [h6421, h7022, h7223, h7228, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7265_1]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [h6422, hlam, p7265_1]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [h7022, hlam, p7265_1]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p7265_1]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [hlam, p7265_0]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    rcases p7265_3 (m.d 0 1) (by simp) with h7273 | h7273
                                    · linarith only [h0, h7273, hlam]
                                    · linarith only [h6421, h7273, hlam]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [h0, h7222, h7233, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p7265_1]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [h0, h6421, h7022, h7223, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7265_1]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [h6421, hlam, p7265_1]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [h7215, hlam, p7265_1]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [hlam, p7265_0]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [h7218, hlam, p7265_1]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [h7220, hlam, p7265_1]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [h6421, h7223, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7265_1]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [h7216, hlam, p7265_0]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [h6421, h6422, h7223, h7226, hc23, hc34, hlam, hphi, p7265_1]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [hlam, p7265_0]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [h6421, h6422, h7022, h7223, h7226, hc23, hc34, hlam, hphi, p7265_1]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [h6421, h7223, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7265_1]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [h7217, hlam, p7265_1]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [h6421, h7022, h7223, h7226, h7228, hc23, hc34, hlam, hphi, p7265_1]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [h7222, hlam, p7265_1]
                                  · have p7265_0 := h7265c.1
                                    have p7265_1 := h7265c.2.1
                                    have p7265_2 := h7265c.2.2.1
                                    have p7265_3 := h7265c.2.2.2
                                    linarith only [hlam, p7265_0]
                                · linarith only [h6421, h6422, h7223, h7226, h7264, hc23, hc45, hlam, hphi, ht34]
                        · linarith only [h6421, h6422, h7222, h7223, h7228, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h7217, h7225, hlam]
                  · linarith only [h0, h7216, h7224, hlam]
                · linarith only [h0, h7215, h7223, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7298 | h7298
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7299 | h7299
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7300 | h7300
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7301 | h7301
                      · linarith only [h6421, h6422, h7222, h7301, hc34, hc45, hlam, hphi]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7303 | h7303
                        · linarith only [h6421, h6422, h7222, h7298, h7301, h7303, hc23, hc34, hlam, hphi]
                        · linarith only [h6421, h6422, h7298, h7303, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h6421, h6422, h7217, h7298, h7299, h7300, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h7216, h7299, hlam]
                · linarith only [h0, h7215, h7298, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7309 | h7309
          · linarith only [h6421, h6422, h7309, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7311 | h7311
            · linarith only [h0, h6421, h7217, h7311, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7313 | h7313
              · linarith only [h7216, h7217, h7313, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7315 | h7315
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7316 | h7316
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7317 | h7317
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7318 | h7318
                      · linarith only [h6421, h6422, h7216, h7217, h7309, h7317, h7318, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7320 | h7320
                        · linarith only [h6421, h6422, h7313, h7315, h7318, h7320, hc23, hc34, hlam, hphi]
                        · linarith only [h6421, h6422, h7315, h7320, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7323 | h7323
                      · linarith only [h0, h6421, h7317, h7323, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7325 | h7325
                        · linarith only [h6422, h7313, h7316, h7317, h7325, hc01, hc25, hlam, hphi, ht12]
                        · linarith only [h6421, h6422, h7315, h7325, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h6421, h7216, h7315, h7316, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h7215, h7315, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h7330 | h7330
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7331 | h7331
          · linarith only [h0, h6421, h7216, h7331, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7333 | h7333
            · linarith only [h6421, h7022, h7333, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7335 | h7335
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7336 | h7336
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7337 | h7337
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7338 | h7338
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7339 | h7339
                      · linarith only [h6421, h7022, h7216, h7330, h7331, h7337, h7339, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7341 | h7341
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7342 | h7342
                          · linarith only [h6421, h7022, h7216, h7330, h7336, h7337, h7339, h7342, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7344 | h7344
                            · linarith only [h6421, h7022, h7333, h7336, h7344, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7346 | h7346
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7347 | h7347
                                · rcases h0bigk with h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c | h7348c
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [hlam, p7348_0]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h0, hlam, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h7022, h7216, h7330, h7337, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h6422, hlam, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h7022, hlam, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h7216, h7337, hc01, hc12, hlam, hphi, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [hlam, p7348_0]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h6421, h7216, h7336, h7337, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h7216, hlam, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h7216, h7337, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h6421, hlam, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h7215, hlam, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [hlam, p7348_0]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h7331, hlam, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h7333, hlam, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h6421, h7336, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h7216, h7337, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h6421, h7216, h7336, h7337, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [hlam, p7348_0]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h6421, h7022, h7216, h7336, h7337, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h6421, h7330, h7336, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h7330, hlam, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h6421, h7216, h7330, h7336, h7337, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [h7335, hlam, p7348_1]
                                  · have p7348_0 := h7348c.1
                                    have p7348_1 := h7348c.2.1
                                    have p7348_2 := h7348c.2.2.1
                                    have p7348_3 := h7348c.2.2.2
                                    linarith only [hlam, p7348_0]
                                · linarith only [h0, h6421, h7216, h7336, h7337, h7339, h7347, hc23, hc45, hlam, hphi, ht34]
                              · linarith only [h7216, h7330, h7335, h7346, hlam]
                        · linarith only [h7216, h7330, h7335, h7337, h7341, hlam]
                    · linarith only [h7216, h7330, h7338, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7378 | h7378
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7379 | h7379
                      · linarith only [h6421, h7022, h7331, h7337, h7378, h7379, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7381 | h7381
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7382 | h7382
                          · linarith only [h6421, h6422, h7022, h7216, h7336, h7337, h7378, h7379, h7382, hc02, hc24, hlam, hphi]
                          · linarith only [h6421, h7022, h7336, h7337, h7378, h7382, hc23, hc34, hlam, hphi]
                        · linarith only [h6421, h7022, h7336, h7337, h7378, h7381, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6421, h7330, h7378, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h7215, h7336, hlam]
              · linarith only [h7216, h7330, h7335, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h7389 | h7389
          · linarith only [h0, h6421, h7216, h7389, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h7391 | h7391
            · linarith only [h0, h6421, h7330, h7391, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7393 | h7393
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7394 | h7394
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7395 | h7395
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7396 | h7396
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7397 | h7397
                      · linarith only [h0, h6421, h7216, h7389, h7395, h7397, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7399 | h7399
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7400 | h7400
                          · linarith only [h0, h6421, h7330, h7394, h7396, h7397, h7399, h7400, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h7402 | h7402
                            · linarith only [h0, h6421, h7330, h7391, h7394, h7402, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h7404 | h7404
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h7405 | h7405
                                · rcases h0bigk with h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c | h7406c
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [hlam, p7406_0]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h0, hlam, p7406_1]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h0, h7330, h7395, h7404, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7406_1]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h6422, hlam, p7406_1]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h7022, hlam, p7406_1]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h7330, h7395, h7404, hc01, hc12, hlam, hphi, p7406_1]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [hlam, p7406_0]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h6421, h7330, h7394, h7395, h7404, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7406_1]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h7216, hlam, p7406_1]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h7330, hlam, p7406_0]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h6421, hlam, p7406_1]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h7215, hlam, p7406_1]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [hlam, p7406_0]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h7389, hlam, p7406_1]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h7391, hlam, p7406_1]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h6421, h7394, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7406_1]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h7216, h7395, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p7406_1]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h6421, h7216, h7394, h7395, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7406_1]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [hlam, p7406_0]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h0, h6421, h7216, h7330, h7394, h7395, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7406_1]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h6421, h7394, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p7406_1]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h0, h6421, h7330, h7394, h7395, h7404, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7406_1]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h6421, h7330, h7394, h7395, h7404, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p7406_1]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [h7393, hlam, p7406_1]
                                  · have p7406_0 := h7406c.1
                                    have p7406_1 := h7406c.2.1
                                    have p7406_2 := h7406c.2.2.1
                                    have p7406_3 := h7406c.2.2.2
                                    linarith only [hlam, p7406_0]
                                · linarith only [h6421, h6422, h7216, h7393, h7394, h7395, h7397, h7405, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · linarith only [h7216, h7393, h7404, hlam]
                        · linarith only [h7216, h7393, h7395, h7399, hlam]
                    · linarith only [h0, h6421, h7216, h7394, h7395, h7396, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7436 | h7436
                    · linarith only [h0, h6421, h7330, h7394, h7395, h7436, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7438 | h7438
                      · linarith only [h0, h6421, h7395, h7438, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7440 | h7440
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h7441 | h7441
                          · linarith only [h0, h6421, h7394, h7436, h7438, h7440, h7441, hlam]
                          · linarith only [h0, h6421, h7394, h7395, h7441, hc23, hc34, hlam, hphi]
                        · linarith only [h6422, h7393, h7440, hlam]
                · linarith only [h0, h7215, h7394, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7446 | h7446
                · rcases m.htr 1 2 4 (by decide) (by decide) with h7447 | h7447
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7448 | h7448
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7449 | h7449
                      · linarith only [h6421, h6422, h7393, h7449, hc34, hc45, hlam, hphi]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7451 | h7451
                        · linarith only [h6421, h6422, h7393, h7449, h7451, hc13, hc34, hlam, hphi]
                        · linarith only [h6421, h6422, h7446, h7451, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h7216, h7447, h7448, hc02, hc25, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h7455 | h7455
                    · linarith only [h0, h6421, h7330, h7446, h7447, h7455, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h7457 | h7457
                      · linarith only [h0, h6421, h7447, h7457, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h7459 | h7459
                        · linarith only [h0, h6421, h7216, h7393, h7446, h7457, h7459, hc23, hc34, hlam, hphi]
                        · linarith only [h6421, h6422, h7446, h7459, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h6421, h7215, h7446, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · linarith only [h0, h6421, h7215, hlam]

set_option maxHeartbeats 9764000 in
set_option maxHeartbeats 9764000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s7_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6421 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h6422 | h6422
  · exact r1l7_20_12_14_H_I_L_I_L_I_s7_x0_x0 m hb0 hb2 hb4 hg0 h6421 h6422
  · exact r1l7_20_12_14_H_I_L_I_L_I_s7_x0_x1 m hb0 hb2 hb4 hg0 h6421 h6422

set_option maxHeartbeats 9764000 in
set_option maxHeartbeats 9764000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s7_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6421 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0 := hg0
  exact r1l7_20_12_14_H_I_L_I_L_I_s8 m hb0 hb2 hb4 h0 h6421

set_option maxHeartbeats 9764000 in
set_option maxHeartbeats 9764000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s7 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h6421 | h6421
  · exact r1l7_20_12_14_H_I_L_I_L_I_s7_x0 m hb0 hb2 hb4 hg0 h6421
  · exact r1l7_20_12_14_H_I_L_I_L_I_s7_x1 m hb0 hb2 hb4 hg0 h6421

set_option maxHeartbeats 22606000 in
set_option maxHeartbeats 22606000 in
theorem r1l7_20_12_14_H_I_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_14_H_I_L_I_L_I_s0 m hb0 hb2 hb4 h0
  · exact r1l7_20_12_14_H_I_L_I_L_I_s7 m hb0 hb2 hb4 h0

end R2N4
