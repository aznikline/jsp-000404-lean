import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 19774000 in
set_option maxHeartbeats 19774000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s22_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg19744 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h22010 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h22011 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h1emax := hb1.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h19744 := hg19744
  rcases m.htr 0 3 5 (by decide) (by decide) with h22012 | h22012
  · rcases m.htr 0 4 5 (by decide) (by decide) with h22013 | h22013
    · rcases m.htr 1 2 3 (by decide) (by decide) with h22014 | h22014
      · linarith only [h0, h22014, h4, hlam]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h22016 | h22016
        · linarith only [h0, h19744, h22016, hlam]
        · rcases m.htr 1 2 5 (by decide) (by decide) with h22018 | h22018
          · rcases m.htr 1 3 4 (by decide) (by decide) with h22019 | h22019
            · rcases m.htr 1 3 5 (by decide) (by decide) with h22020 | h22020
              · rcases m.htr 1 4 5 (by decide) (by decide) with h22021 | h22021
                · rcases m.htr 2 3 4 (by decide) (by decide) with h22022 | h22022
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h22023 | h22023
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h22024 | h22024
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h22025 | h22025
                        · rcases h1bigk with h22026c | h22026c | h22026c | h22026c | h22026c | h22026c | h22026c | h22026c | h22026c | h22026c | h22026c | h22026c | h22026c | h22026c | h22026c | h22026c | h22026c | h22026c | h22026c | h22026c | h22026c | h22026c | h22026c | h22026c | h22026c
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            linarith only [hlam, p22026_0]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            rcases p22026_3 (m.d 0 1) (by simp) with h22028 | h22028
                            · rcases p22026_3 (m.d 1 2) (by simp) with h22029 | h22029
                              · linarith only [h22029, hlam, p22026_0]
                              · rcases p22026_3 (m.d 1 3) (by simp) with h22031 | h22031
                                · linarith only [h1, h22031, hlam]
                                · linarith only [h22014, h22031, hlam]
                            · linarith only [h22028, hlam, p22026_0]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            linarith only [h22019, h22025, hc01, hc45, hlam, hphi, ht0b, ht5b, p22026_1]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            rcases p22026_3 (m.d 0 1) (by simp) with h22036 | h22036
                            · rcases p22026_3 (m.d 1 2) (by simp) with h22037 | h22037
                              · linarith only [h0, h22037, hlam]
                              · rcases p22026_3 (m.d 1 3) (by simp) with h22039 | h22039
                                · linarith only [h1, h22039, hlam]
                                · linarith only [h22019, h22039, hlam]
                            · linarith only [h22036, hlam, p22026_0]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            rcases p22026_3 (m.d 0 1) (by simp) with h22043 | h22043
                            · rcases p22026_3 (m.d 1 2) (by simp) with h22044 | h22044
                              · linarith only [h0, h22044, hlam]
                              · linarith only [h22018, h22044, hlam]
                            · linarith only [h22043, hlam, p22026_0]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            linarith only [h0, hlam, p22026_0]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            linarith only [hlam, p22026_0]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            linarith only [h22014, hlam, p22026_1]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            linarith only [h22016, hlam, p22026_1]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            rcases p22026_3 (m.d 0 1) (by simp) with h22052 | h22052
                            · rcases p22026_3 (m.d 1 2) (by simp) with h22053 | h22053
                              · rcases p22026_3 (m.d 1 3) (by simp) with h22054 | h22054
                                · rcases p22026_3 (m.d 1 4) (by simp) with h22055 | h22055
                                  · rcases p22026_3 (m.d 1 5) (by simp) with h22056 | h22056
                                    · linarith only [h22018, h22056, hlam]
                                    · rcases h1emax with h22058 | h22058 | h22058 | h22058 | h22058
                                      · linarith only [h0, h22018, h22023, h22025, h22058, hc45, hlam, hphi, ht01, ht0b, ht5b, p22026_1]
                                      · linarith only [h22018, h22023, h22025, h22058, hc45, hlam, hphi, ht01, ht0b, ht5b, p22026_1]
                                      · linarith only [h22016, h22018, h22019, h22023, h22025, h22058, hc45, hlam, hphi, ht01, ht0b, ht5b, p22026_1]
                                      · linarith only [h22016, h22018, h22023, h22025, h22058, hc45, hlam, hphi, ht01, ht0b, ht5b, p22026_1]
                                      · rcases h2bigk with h22063c | h22063c | h22063c | h22063c | h22063c | h22063c | h22063c | h22063c | h22063c | h22063c | h22063c | h22063c | h22063c | h22063c | h22063c | h22063c | h22063c | h22063c | h22063c | h22063c | h22063c | h22063c | h22063c | h22063c | h22063c
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [hlam, p22063_0]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [h22018, h22023, h22025, hc02, hc45, hlam, hphi, ht0b, ht5b, p22026_1, p22063_1]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [h4, hlam, p22063_0]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [h19744, hlam, p22063_0]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          rcases p22063_3 (m.d 0 2) (by simp) with h22068 | h22068
                                          · rcases p22063_3 (m.d 1 2) (by simp) with h22069 | h22069
                                            · linarith only [h0, h22069, hlam]
                                            · linarith only [h22018, h22069, hlam]
                                          · linarith only [h22068, hlam, p22063_0]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [h0, hlam, p22063_1]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [hlam, p22063_0]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [h22014, hlam, p22063_0]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [h22016, hlam, p22063_0]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          rcases p22063_3 (m.d 0 2) (by simp) with h22077 | h22077
                                          · rcases p22063_3 (m.d 1 2) (by simp) with h22078 | h22078
                                            · rcases p22063_3 (m.d 2 3) (by simp) with h22079 | h22079
                                              · rcases p22063_3 (m.d 2 4) (by simp) with h22080 | h22080
                                                · rcases p22063_3 (m.d 2 5) (by simp) with h22081 | h22081
                                                  · linarith only [h22081, hlam, p22063_0]
                                                  · rcases h4bigk with h22083c | h22083c | h22083c | h22083c | h22083c | h22083c | h22083c | h22083c | h22083c | h22083c | h22083c | h22083c | h22083c | h22083c | h22083c | h22083c | h22083c | h22083c | h22083c | h22083c | h22083c | h22083c | h22083c | h22083c | h22083c
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [hlam, p22083_0]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [h22011, h22016, h22018, h22023, h22025, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22026_1, p22083_1]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [h19744, hlam, p22083_1]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      rcases p22083_3 (m.d 0 4) (by simp) with h22087 | h22087
                                                      · rcases p22083_3 (m.d 1 4) (by simp) with h22088 | h22088
                                                        · linarith only [h2, h22088, hlam]
                                                        · linarith only [h22019, h22088, hlam]
                                                      · linarith only [h22011, h22087, hlam]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      rcases p22083_3 (m.d 0 4) (by simp) with h22092 | h22092
                                                      · rcases p22083_3 (m.d 1 4) (by simp) with h22093 | h22093
                                                        · linarith only [h2, h22093, hlam]
                                                        · linarith only [h22021, h22093, hlam]
                                                      · linarith only [h22092, hlam, p22083_0]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [h2, hlam, p22083_0]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [hlam, p22083_0]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [h22016, hlam, p22083_1]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [h1, h22019, h22025, hc01, hc45, hlam, hphi, ht0b, ht5b, p22083_1]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      rcases p22083_3 (m.d 0 4) (by simp) with h22101 | h22101
                                                      · rcases p22083_3 (m.d 1 4) (by simp) with h22102 | h22102
                                                        · rcases p22083_3 (m.d 2 4) (by simp) with h22103 | h22103
                                                          · rcases p22083_3 (m.d 3 4) (by simp) with h22104 | h22104
                                                            · linarith only [h22019, h22104, hlam]
                                                            · linarith only [h22025, h22104, hlam]
                                                          · linarith only [h22024, h22103, hlam]
                                                        · linarith only [h22102, hlam, p22083_0]
                                                      · linarith only [h22013, h22101, hlam]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [h0, h19744, h22018, h22022, h22023, h22025, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22026_1, p22083_1]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [h22016, h22018, h22022, h22023, h22025, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22026_1, p22083_1]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [hlam, p22083_0]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      rcases p22083_3 (m.d 0 4) (by simp) with h22113 | h22113
                                                      · linarith only [h19744, h22113, hlam]
                                                      · linarith only [h22011, h22113, hlam]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [h0, h19744, h22018, h22023, h22025, hlam, p22026_1, p22083_2]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [h22011, hlam, p22083_0]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [h22019, hlam, p22083_0]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [h22022, hlam, p22083_0]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [hlam, p22083_0]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [h1, h22019, hc01, hc45, hlam, hphi, ht0b, ht5b, p22083_1]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [h22013, hlam, p22083_0]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [h22021, hlam, p22083_0]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [h22024, hlam, p22083_0]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [h22025, hlam, p22083_0]
                                                    · have p22083_0 := h22083c.1
                                                      have p22083_1 := h22083c.2.1
                                                      have p22083_2 := h22083c.2.2.1
                                                      have p22083_3 := h22083c.2.2.2
                                                      linarith only [hlam, p22083_0]
                                                · linarith only [h22024, h22080, hlam]
                                              · linarith only [h22023, h22079, hlam]
                                            · linarith only [h22078, hlam, p22063_0]
                                          · linarith only [h22010, h22077, hlam]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [h0, h22018, h22023, h22025, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22026_1, p22063_1]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [h22018, h22023, h22025, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22026_1, p22063_1]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [hlam, p22063_0]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [h0, h19744, h22018, h22023, h22025, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22026_1, p22063_1]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [h0, h22018, h4, hlam, p22026_1, p22063_2]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [h0, h22018, h22023, h22025, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22026_1, p22063_1]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [h22018, h22023, h22025, hc24, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22026_1, p22063_1]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [h22022, hlam, p22063_0]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [hlam, p22063_0]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [h0, h19744, h22018, hlam, p22026_1, p22063_2]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [h22010, hlam, p22063_0]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [h22018, hlam, p22063_0]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [h22023, hlam, p22063_0]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [h22024, hlam, p22063_1]
                                        · have p22063_0 := h22063c.1
                                          have p22063_1 := h22063c.2.1
                                          have p22063_2 := h22063c.2.2.1
                                          have p22063_3 := h22063c.2.2.2
                                          linarith only [hlam, p22063_0]
                                  · linarith only [h22021, h22055, hlam]
                                · linarith only [h22020, h22054, hlam]
                              · linarith only [h22018, h22053, hlam]
                            · linarith only [h22052, h3, hlam]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            linarith only [h1, hlam, p22026_0]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            linarith only [h1, h22018, h22023, h22025, hc01, hc45, hlam, hphi, ht0b, ht5b, p22026_1]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            linarith only [hlam, p22026_0]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            linarith only [h1, h22016, h22018, h22023, h22025, hc01, hc45, hlam, hphi, ht0b, ht5b, p22026_1]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            rcases p22026_3 (m.d 0 1) (by simp) with h22154 | h22154
                            · rcases p22026_3 (m.d 1 2) (by simp) with h22155 | h22155
                              · linarith only [h22014, h22155, hlam]
                              · linarith only [h22018, h22155, hlam]
                            · linarith only [h22154, h3, hlam]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            linarith only [h2, hlam, p22026_0]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            linarith only [h2, h22018, h22023, h22025, hc01, hc45, hlam, hphi, ht0b, ht5b, p22026_1]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            linarith only [h22019, hlam, p22026_1]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            linarith only [hlam, p22026_0]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            rcases p22026_3 (m.d 0 1) (by simp) with h22163 | h22163
                            · rcases p22026_3 (m.d 1 2) (by simp) with h22164 | h22164
                              · linarith only [h22016, h22164, hlam]
                              · linarith only [h22018, h22164, hlam]
                            · linarith only [h22163, h3, hlam]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            linarith only [h3, hlam, p22026_0]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            linarith only [h22018, hlam, p22026_0]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            linarith only [h22020, hlam, p22026_0]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            linarith only [h22021, hlam, p22026_0]
                          · have p22026_0 := h22026c.1
                            have p22026_1 := h22026c.2.1
                            have p22026_2 := h22026c.2.2.1
                            have p22026_3 := h22026c.2.2.2
                            linarith only [hlam, p22026_0]
                        · rcases h1bigk with h22173c | h22173c | h22173c | h22173c | h22173c | h22173c | h22173c | h22173c | h22173c | h22173c | h22173c | h22173c | h22173c | h22173c | h22173c | h22173c | h22173c | h22173c | h22173c | h22173c | h22173c | h22173c | h22173c | h22173c | h22173c
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [hlam, p22173_0]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [h22018, h22024, h22025, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22173_1]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [h22016, h22018, h22019, h22024, h22025, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22173_1]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [h22016, h22018, h22024, h22025, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22173_1]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            rcases p22173_3 (m.d 0 1) (by simp) with h22178 | h22178
                            · rcases p22173_3 (m.d 1 2) (by simp) with h22179 | h22179
                              · linarith only [h0, h22179, hlam]
                              · linarith only [h22018, h22179, hlam]
                            · linarith only [h22178, hlam, p22173_0]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [h0, hlam, p22173_0]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [hlam, p22173_0]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [h22014, hlam, p22173_1]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [h22016, hlam, p22173_1]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [h0, h19744, h22018, h22022, h22024, h22025, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p22173_1]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [h1, hlam, p22173_0]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [h1, h22018, h22024, h22025, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22173_1]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [hlam, p22173_0]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [h1, h22016, h22018, h22024, h22025, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22173_1]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [h1, h22018, h22024, h22025, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22173_1]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [h2, hlam, p22173_0]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [h22018, h22024, h22025, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p22173_1]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [h22019, hlam, p22173_1]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [hlam, p22173_0]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [h2, h22018, h22024, h22025, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p22173_1]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [h3, hlam, p22173_0]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [h22018, hlam, p22173_0]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [h22020, hlam, p22173_0]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [h22021, hlam, p22173_0]
                          · have p22173_0 := h22173c.1
                            have p22173_1 := h22173c.2.1
                            have p22173_2 := h22173c.2.2.1
                            have p22173_3 := h22173c.2.2.2
                            linarith only [hlam, p22173_0]
                      · linarith only [h0, h19744, h22018, h22021, h22024, h3, hc01, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h22012, h22023, h4, hlam]
                  · linarith only [h22011, h22022, h4, hlam]
                · linarith only [h22016, h22018, h22021, hlam]
              · linarith only [h22016, h22018, h22019, h22020, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h22208 | h22208
              · rcases m.htr 1 4 5 (by decide) (by decide) with h22209 | h22209
                · rcases m.htr 2 3 4 (by decide) (by decide) with h22210 | h22210
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h22211 | h22211
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h22212 | h22212
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h22213 | h22213
                        · rcases h1bigk with h22214c | h22214c | h22214c | h22214c | h22214c | h22214c | h22214c | h22214c | h22214c | h22214c | h22214c | h22214c | h22214c | h22214c | h22214c | h22214c | h22214c | h22214c | h22214c | h22214c | h22214c | h22214c | h22214c | h22214c | h22214c
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [hlam, p22214_0]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            rcases p22214_3 (m.d 0 1) (by simp) with h22216 | h22216
                            · rcases p22214_3 (m.d 1 2) (by simp) with h22217 | h22217
                              · linarith only [h22217, hlam, p22214_0]
                              · rcases p22214_3 (m.d 1 3) (by simp) with h22219 | h22219
                                · linarith only [h1, h22219, hlam]
                                · linarith only [h22014, h22219, hlam]
                            · linarith only [h22216, hlam, p22214_0]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            rcases p22214_3 (m.d 0 1) (by simp) with h22223 | h22223
                            · rcases p22214_3 (m.d 1 2) (by simp) with h22224 | h22224
                              · linarith only [h0, h22224, hlam]
                              · rcases p22214_3 (m.d 1 3) (by simp) with h22226 | h22226
                                · linarith only [h22226, hlam, p22214_0]
                                · rcases p22214_3 (m.d 1 4) (by simp) with h22228 | h22228
                                  · linarith only [h2, h22228, hlam]
                                  · linarith only [h22019, h22228, hlam]
                            · linarith only [h22223, hlam, p22214_0]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            rcases p22214_3 (m.d 0 1) (by simp) with h22232 | h22232
                            · rcases p22214_3 (m.d 1 2) (by simp) with h22233 | h22233
                              · linarith only [h0, h22233, hlam]
                              · rcases p22214_3 (m.d 1 3) (by simp) with h22235 | h22235
                                · linarith only [h1, h22235, hlam]
                                · rcases p22214_3 (m.d 1 4) (by simp) with h22237 | h22237
                                  · linarith only [h22237, hlam, p22214_0]
                                  · rcases p22214_3 (m.d 1 5) (by simp) with h22239 | h22239
                                    · linarith only [h22239, h3, hlam]
                                    · rcases h1emax with h22241 | h22241 | h22241 | h22241 | h22241
                                      · linarith only [h1, h22011, h22019, h22241, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                      · rcases h2bigk with h22243c | h22243c | h22243c | h22243c | h22243c | h22243c | h22243c | h22243c | h22243c | h22243c | h22243c | h22243c | h22243c | h22243c | h22243c | h22243c | h22243c | h22243c | h22243c | h22243c | h22243c | h22243c | h22243c | h22243c | h22243c
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          linarith only [hlam, p22243_0]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          linarith only [h19744, h22018, h22210, h22211, h22213, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22243_1]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          linarith only [h4, hlam, p22243_0]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          linarith only [h19744, hlam, p22243_0]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          rcases p22243_3 (m.d 0 2) (by simp) with h22248 | h22248
                                          · rcases p22243_3 (m.d 1 2) (by simp) with h22249 | h22249
                                            · linarith only [h0, h22249, hlam]
                                            · linarith only [h22018, h22249, hlam]
                                          · linarith only [h22248, hlam, p22243_0]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          linarith only [h0, hlam, p22243_1]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          linarith only [hlam, p22243_0]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          linarith only [h22014, hlam, p22243_0]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          linarith only [h22016, hlam, p22243_0]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          linarith only [h1, h22011, h22014, h22019, h22211, h22213, hc01, hc45, hlam, hphi, ht0b, ht5b, p22243_1]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          rcases p22243_3 (m.d 0 2) (by simp) with h22258 | h22258
                                          · linarith only [h22258, hlam, p22243_0]
                                          · rcases p22243_3 (m.d 1 2) (by simp) with h22260 | h22260
                                            · linarith only [h22014, h22260, hlam]
                                            · rcases p22243_3 (m.d 2 3) (by simp) with h22262 | h22262
                                              · rcases p22243_3 (m.d 2 4) (by simp) with h22263 | h22263
                                                · linarith only [h22210, h22263, hlam]
                                                · linarith only [h19744, h22263, hlam]
                                              · linarith only [h22262, hlam, p22243_0]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          rcases p22243_3 (m.d 0 2) (by simp) with h22267 | h22267
                                          · linarith only [h22267, h4, hlam]
                                          · linarith only [h0, h22267, hlam]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          linarith only [hlam, p22243_0]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          linarith only [h19744, hc02, hc23, hlam, hphi, p22243_1]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          linarith only [h22011, h22014, h22018, h22019, h4, hlam, p22243_2]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          rcases p22243_3 (m.d 0 2) (by simp) with h22273 | h22273
                                          · linarith only [h22273, hlam, p22243_0]
                                          · rcases p22243_3 (m.d 1 2) (by simp) with h22275 | h22275
                                            · linarith only [h22016, h22275, hlam]
                                            · rcases p22243_3 (m.d 2 3) (by simp) with h22277 | h22277
                                              · rcases p22243_3 (m.d 2 4) (by simp) with h22278 | h22278
                                                · rcases p22243_3 (m.d 2 5) (by simp) with h22279 | h22279
                                                  · linarith only [h22212, h22279, hlam]
                                                  · rcases h4bigk with h22281c | h22281c | h22281c | h22281c | h22281c | h22281c | h22281c | h22281c | h22281c | h22281c | h22281c | h22281c | h22281c | h22281c | h22281c | h22281c | h22281c | h22281c | h22281c | h22281c | h22281c | h22281c | h22281c | h22281c | h22281c
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [hlam, p22281_0]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      rcases p22281_3 (m.d 0 4) (by simp) with h22283 | h22283
                                                      · rcases p22281_3 (m.d 1 4) (by simp) with h22284 | h22284
                                                        · linarith only [h2, h22284, hlam]
                                                        · rcases p22281_3 (m.d 2 4) (by simp) with h22286 | h22286
                                                          · rcases p22281_3 (m.d 3 4) (by simp) with h22287 | h22287
                                                            · linarith only [h22011, h22287, hlam]
                                                            · linarith only [h22019, h22287, hlam]
                                                          · linarith only [h22016, h22286, hlam]
                                                      · linarith only [h2, h22283, hlam]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [h19744, hlam, p22281_1]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [h19744, h22014, h22019, h22210, hc12, hc23, hlam, hphi, p22281_1]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      rcases p22281_3 (m.d 0 4) (by simp) with h22294 | h22294
                                                      · rcases p22281_3 (m.d 1 4) (by simp) with h22295 | h22295
                                                        · linarith only [h2, h22295, hlam]
                                                        · linarith only [h22209, h22295, hlam]
                                                      · linarith only [h22294, hlam, p22281_0]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [h2, hlam, p22281_0]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [hlam, p22281_0]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [h22016, hlam, p22281_1]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [h22019, hlam, p22281_1]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p22214_1, p22281_1]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [h22011, h22014, h22018, h22019, h22210, h22211, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p22281_1]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      rcases p22281_3 (m.d 0 4) (by simp) with h22305 | h22305
                                                      · linarith only [h19744, h22305, hlam]
                                                      · linarith only [h2, h22305, hlam]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [hlam, p22281_0]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [h22014, h22018, h22019, h22210, h22211, h22213, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22281_1]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [h0, h22018, h22211, h22213, hlam, p22243_1, p22281_2]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [h22011, hlam, p22281_0]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [h1, h22011, hlam, p22214_2, p22281_1]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [h22210, hlam, p22281_0]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [hlam, p22281_0]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      rcases p22281_3 (m.d 0 4) (by simp) with h22315 | h22315
                                                      · rcases p22281_3 (m.d 1 4) (by simp) with h22316 | h22316
                                                        · linarith only [h22019, h22316, hlam]
                                                        · linarith only [h22209, h22316, hlam]
                                                      · linarith only [h22013, h22315, hlam]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [h22013, hlam, p22281_0]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [h22209, hlam, p22281_0]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [h22212, hlam, p22281_0]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [h22213, hlam, p22281_0]
                                                    · have p22281_0 := h22281c.1
                                                      have p22281_1 := h22281c.2.1
                                                      have p22281_2 := h22281c.2.2.1
                                                      have p22281_3 := h22281c.2.2.2
                                                      linarith only [hlam, p22281_0]
                                                · linarith only [h22278, hlam, p22243_0]
                                              · linarith only [h22277, h4, hlam]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          rcases p22243_3 (m.d 0 2) (by simp) with h22327 | h22327
                                          · linarith only [h19744, h22327, hlam]
                                          · linarith only [h0, h22327, hlam]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          linarith only [h22210, hlam, p22243_0]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          linarith only [hlam, p22243_0]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          rcases p22243_3 (m.d 0 2) (by simp) with h22332 | h22332
                                          · linarith only [h19744, h22332, hlam]
                                          · linarith only [h22010, h22332, hlam]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          linarith only [h22010, hlam, p22243_0]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          linarith only [h22018, hlam, p22243_0]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          linarith only [h22211, hlam, p22243_0]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          linarith only [h22212, hlam, p22243_1]
                                        · have p22243_0 := h22243c.1
                                          have p22243_1 := h22243c.2.1
                                          have p22243_2 := h22243c.2.2.1
                                          have p22243_3 := h22243c.2.2.2
                                          linarith only [hlam, p22243_0]
                                      · rcases h2bigk with h22340c | h22340c | h22340c | h22340c | h22340c | h22340c | h22340c | h22340c | h22340c | h22340c | h22340c | h22340c | h22340c | h22340c | h22340c | h22340c | h22340c | h22340c | h22340c | h22340c | h22340c | h22340c | h22340c | h22340c | h22340c
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          linarith only [hlam, p22340_0]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          linarith only [h22018, h22211, h22213, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22340_1]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          linarith only [h4, hlam, p22340_0]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          linarith only [h19744, hlam, p22340_0]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          rcases p22340_3 (m.d 0 2) (by simp) with h22345 | h22345
                                          · rcases p22340_3 (m.d 1 2) (by simp) with h22346 | h22346
                                            · linarith only [h0, h22346, hlam]
                                            · linarith only [h22018, h22346, hlam]
                                          · linarith only [h22345, hlam, p22340_0]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          linarith only [h0, hlam, p22340_1]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          linarith only [hlam, p22340_0]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          linarith only [h22014, hlam, p22340_0]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          linarith only [h22016, hlam, p22340_0]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          linarith only [h1, h22011, h22014, h22019, h22211, h22213, hc01, hc45, hlam, hphi, ht0b, ht5b, p22340_1]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          rcases p22340_3 (m.d 0 2) (by simp) with h22355 | h22355
                                          · linarith only [h22355, hlam, p22340_0]
                                          · rcases p22340_3 (m.d 1 2) (by simp) with h22357 | h22357
                                            · linarith only [h22014, h22357, hlam]
                                            · rcases p22340_3 (m.d 2 3) (by simp) with h22359 | h22359
                                              · rcases p22340_3 (m.d 2 4) (by simp) with h22360 | h22360
                                                · linarith only [h22210, h22360, hlam]
                                                · linarith only [h19744, h22360, hlam]
                                              · linarith only [h22359, hlam, p22340_0]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          rcases p22340_3 (m.d 0 2) (by simp) with h22364 | h22364
                                          · linarith only [h22364, h4, hlam]
                                          · linarith only [h0, h22364, hlam]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          linarith only [hlam, p22340_0]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          linarith only [h19744, hc02, hc23, hlam, hphi, p22340_1]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          linarith only [h22011, h22014, h22018, h22019, h4, hlam, p22340_2]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          rcases p22340_3 (m.d 0 2) (by simp) with h22370 | h22370
                                          · linarith only [h22370, hlam, p22340_0]
                                          · rcases p22340_3 (m.d 1 2) (by simp) with h22372 | h22372
                                            · linarith only [h22016, h22372, hlam]
                                            · rcases p22340_3 (m.d 2 3) (by simp) with h22374 | h22374
                                              · rcases p22340_3 (m.d 2 4) (by simp) with h22375 | h22375
                                                · rcases p22340_3 (m.d 2 5) (by simp) with h22376 | h22376
                                                  · linarith only [h22212, h22376, hlam]
                                                  · rcases h4bigk with h22378c | h22378c | h22378c | h22378c | h22378c | h22378c | h22378c | h22378c | h22378c | h22378c | h22378c | h22378c | h22378c | h22378c | h22378c | h22378c | h22378c | h22378c | h22378c | h22378c | h22378c | h22378c | h22378c | h22378c | h22378c
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [hlam, p22378_0]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      rcases p22378_3 (m.d 0 4) (by simp) with h22380 | h22380
                                                      · rcases p22378_3 (m.d 1 4) (by simp) with h22381 | h22381
                                                        · linarith only [h2, h22381, hlam]
                                                        · rcases p22378_3 (m.d 2 4) (by simp) with h22383 | h22383
                                                          · rcases p22378_3 (m.d 3 4) (by simp) with h22384 | h22384
                                                            · linarith only [h22011, h22384, hlam]
                                                            · linarith only [h22019, h22384, hlam]
                                                          · linarith only [h22016, h22383, hlam]
                                                      · linarith only [h2, h22380, hlam]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [h19744, hlam, p22378_1]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [h19744, h22014, h22019, h22210, hc12, hc23, hlam, hphi, p22378_1]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      rcases p22378_3 (m.d 0 4) (by simp) with h22391 | h22391
                                                      · rcases p22378_3 (m.d 1 4) (by simp) with h22392 | h22392
                                                        · linarith only [h2, h22392, hlam]
                                                        · linarith only [h22209, h22392, hlam]
                                                      · linarith only [h22391, hlam, p22378_0]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [h2, hlam, p22378_0]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [hlam, p22378_0]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [h22016, hlam, p22378_1]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [h22019, hlam, p22378_1]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p22214_1, p22378_1]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [h22011, h22014, h22018, h22019, h22210, h22211, h22213, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22378_1]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      rcases p22378_3 (m.d 0 4) (by simp) with h22402 | h22402
                                                      · linarith only [h19744, h22402, hlam]
                                                      · linarith only [h2, h22402, hlam]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [hlam, p22378_0]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [h22014, h22018, h22019, h22210, h22211, h22213, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22378_1]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [h0, h22018, h22211, h22213, hlam, p22340_1, p22378_2]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [h22011, hlam, p22378_0]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [h1, h22011, hlam, p22214_2, p22378_1]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [h22210, hlam, p22378_0]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [hlam, p22378_0]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      rcases p22378_3 (m.d 0 4) (by simp) with h22412 | h22412
                                                      · rcases p22378_3 (m.d 1 4) (by simp) with h22413 | h22413
                                                        · linarith only [h22019, h22413, hlam]
                                                        · linarith only [h22209, h22413, hlam]
                                                      · linarith only [h22013, h22412, hlam]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [h22013, hlam, p22378_0]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [h22209, hlam, p22378_0]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [h22212, hlam, p22378_0]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [h22213, hlam, p22378_0]
                                                    · have p22378_0 := h22378c.1
                                                      have p22378_1 := h22378c.2.1
                                                      have p22378_2 := h22378c.2.2.1
                                                      have p22378_3 := h22378c.2.2.2
                                                      linarith only [hlam, p22378_0]
                                                · linarith only [h22375, hlam, p22340_0]
                                              · linarith only [h22374, h4, hlam]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          rcases p22340_3 (m.d 0 2) (by simp) with h22424 | h22424
                                          · linarith only [h19744, h22424, hlam]
                                          · linarith only [h0, h22424, hlam]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          linarith only [h22210, hlam, p22340_0]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          linarith only [hlam, p22340_0]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          rcases p22340_3 (m.d 0 2) (by simp) with h22429 | h22429
                                          · linarith only [h19744, h22429, hlam]
                                          · linarith only [h22010, h22429, hlam]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          linarith only [h22010, hlam, p22340_0]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          linarith only [h22018, hlam, p22340_0]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          linarith only [h22211, hlam, p22340_0]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          linarith only [h22212, hlam, p22340_1]
                                        · have p22340_0 := h22340c.1
                                          have p22340_1 := h22340c.2.1
                                          have p22340_2 := h22340c.2.2.1
                                          have p22340_3 := h22340c.2.2.2
                                          linarith only [hlam, p22340_0]
                                      · rcases h2bigk with h22437c | h22437c | h22437c | h22437c | h22437c | h22437c | h22437c | h22437c | h22437c | h22437c | h22437c | h22437c | h22437c | h22437c | h22437c | h22437c | h22437c | h22437c | h22437c | h22437c | h22437c | h22437c | h22437c | h22437c | h22437c
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          linarith only [hlam, p22437_0]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          linarith only [h22018, h22211, h22213, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22437_1]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          linarith only [h4, hlam, p22437_0]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          linarith only [h19744, hlam, p22437_0]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          rcases p22437_3 (m.d 0 2) (by simp) with h22442 | h22442
                                          · rcases p22437_3 (m.d 1 2) (by simp) with h22443 | h22443
                                            · linarith only [h0, h22443, hlam]
                                            · linarith only [h22018, h22443, hlam]
                                          · linarith only [h22442, hlam, p22437_0]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          linarith only [h0, hlam, p22437_1]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          linarith only [hlam, p22437_0]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          linarith only [h22014, hlam, p22437_0]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          linarith only [h22016, hlam, p22437_0]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          linarith only [h1, h22011, h22014, h22019, h22211, h22213, hc01, hc45, hlam, hphi, ht0b, ht5b, p22437_1]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          rcases p22437_3 (m.d 0 2) (by simp) with h22452 | h22452
                                          · linarith only [h22452, hlam, p22437_0]
                                          · rcases p22437_3 (m.d 1 2) (by simp) with h22454 | h22454
                                            · linarith only [h22014, h22454, hlam]
                                            · rcases p22437_3 (m.d 2 3) (by simp) with h22456 | h22456
                                              · rcases p22437_3 (m.d 2 4) (by simp) with h22457 | h22457
                                                · linarith only [h22210, h22457, hlam]
                                                · linarith only [h19744, h22457, hlam]
                                              · linarith only [h22456, hlam, p22437_0]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          rcases p22437_3 (m.d 0 2) (by simp) with h22461 | h22461
                                          · linarith only [h22461, h4, hlam]
                                          · linarith only [h0, h22461, hlam]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          linarith only [hlam, p22437_0]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          linarith only [h19744, hc02, hc23, hlam, hphi, p22437_1]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          linarith only [h22011, h22014, h22018, h22019, h4, hlam, p22437_2]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          rcases p22437_3 (m.d 0 2) (by simp) with h22467 | h22467
                                          · linarith only [h22467, hlam, p22437_0]
                                          · rcases p22437_3 (m.d 1 2) (by simp) with h22469 | h22469
                                            · linarith only [h22016, h22469, hlam]
                                            · rcases p22437_3 (m.d 2 3) (by simp) with h22471 | h22471
                                              · rcases p22437_3 (m.d 2 4) (by simp) with h22472 | h22472
                                                · rcases p22437_3 (m.d 2 5) (by simp) with h22473 | h22473
                                                  · linarith only [h22212, h22473, hlam]
                                                  · rcases h4bigk with h22475c | h22475c | h22475c | h22475c | h22475c | h22475c | h22475c | h22475c | h22475c | h22475c | h22475c | h22475c | h22475c | h22475c | h22475c | h22475c | h22475c | h22475c | h22475c | h22475c | h22475c | h22475c | h22475c | h22475c | h22475c
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [hlam, p22475_0]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      rcases p22475_3 (m.d 0 4) (by simp) with h22477 | h22477
                                                      · rcases p22475_3 (m.d 1 4) (by simp) with h22478 | h22478
                                                        · linarith only [h2, h22478, hlam]
                                                        · rcases p22475_3 (m.d 2 4) (by simp) with h22480 | h22480
                                                          · rcases p22475_3 (m.d 3 4) (by simp) with h22481 | h22481
                                                            · linarith only [h22011, h22481, hlam]
                                                            · linarith only [h22019, h22481, hlam]
                                                          · linarith only [h22016, h22480, hlam]
                                                      · linarith only [h2, h22477, hlam]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [h19744, hlam, p22475_1]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [h19744, h22014, h22019, h22210, hc12, hc23, hlam, hphi, p22475_1]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      rcases p22475_3 (m.d 0 4) (by simp) with h22488 | h22488
                                                      · rcases p22475_3 (m.d 1 4) (by simp) with h22489 | h22489
                                                        · linarith only [h2, h22489, hlam]
                                                        · linarith only [h22209, h22489, hlam]
                                                      · linarith only [h22488, hlam, p22475_0]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [h2, hlam, p22475_0]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [hlam, p22475_0]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [h22016, hlam, p22475_1]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [h22019, hlam, p22475_1]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p22214_1, p22475_1]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [h22011, h22014, h22018, h22019, h22210, h22211, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p22475_1]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      rcases p22475_3 (m.d 0 4) (by simp) with h22499 | h22499
                                                      · linarith only [h19744, h22499, hlam]
                                                      · linarith only [h2, h22499, hlam]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [hlam, p22475_0]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [h22014, h22018, h22019, h22210, h22211, h22213, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22475_1]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [h0, h22018, h22211, h22213, hlam, p22437_1, p22475_2]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [h22011, hlam, p22475_0]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [h1, h22011, hlam, p22214_2, p22475_1]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [h22210, hlam, p22475_0]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [hlam, p22475_0]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      rcases p22475_3 (m.d 0 4) (by simp) with h22509 | h22509
                                                      · rcases p22475_3 (m.d 1 4) (by simp) with h22510 | h22510
                                                        · linarith only [h22019, h22510, hlam]
                                                        · linarith only [h22209, h22510, hlam]
                                                      · linarith only [h22013, h22509, hlam]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [h22013, hlam, p22475_0]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [h22209, hlam, p22475_0]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [h22212, hlam, p22475_0]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [h22213, hlam, p22475_0]
                                                    · have p22475_0 := h22475c.1
                                                      have p22475_1 := h22475c.2.1
                                                      have p22475_2 := h22475c.2.2.1
                                                      have p22475_3 := h22475c.2.2.2
                                                      linarith only [hlam, p22475_0]
                                                · linarith only [h22472, hlam, p22437_0]
                                              · linarith only [h22471, h4, hlam]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          rcases p22437_3 (m.d 0 2) (by simp) with h22521 | h22521
                                          · linarith only [h19744, h22521, hlam]
                                          · linarith only [h0, h22521, hlam]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          linarith only [h22210, hlam, p22437_0]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          linarith only [hlam, p22437_0]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          rcases p22437_3 (m.d 0 2) (by simp) with h22526 | h22526
                                          · linarith only [h19744, h22526, hlam]
                                          · linarith only [h22010, h22526, hlam]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          linarith only [h22010, hlam, p22437_0]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          linarith only [h22018, hlam, p22437_0]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          linarith only [h22211, hlam, p22437_0]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          linarith only [h22212, hlam, p22437_1]
                                        · have p22437_0 := h22437c.1
                                          have p22437_1 := h22437c.2.1
                                          have p22437_2 := h22437c.2.2.1
                                          have p22437_3 := h22437c.2.2.2
                                          linarith only [hlam, p22437_0]
                                      · rcases h2bigk with h22534c | h22534c | h22534c | h22534c | h22534c | h22534c | h22534c | h22534c | h22534c | h22534c | h22534c | h22534c | h22534c | h22534c | h22534c | h22534c | h22534c | h22534c | h22534c | h22534c | h22534c | h22534c | h22534c | h22534c | h22534c
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          linarith only [hlam, p22534_0]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          linarith only [h22018, h22211, h22213, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22534_1]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          linarith only [h4, hlam, p22534_0]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          linarith only [h19744, hlam, p22534_0]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          rcases p22534_3 (m.d 0 2) (by simp) with h22539 | h22539
                                          · rcases p22534_3 (m.d 1 2) (by simp) with h22540 | h22540
                                            · linarith only [h0, h22540, hlam]
                                            · linarith only [h22018, h22540, hlam]
                                          · linarith only [h22539, hlam, p22534_0]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          linarith only [h0, hlam, p22534_1]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          linarith only [hlam, p22534_0]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          linarith only [h22014, hlam, p22534_0]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          linarith only [h22016, hlam, p22534_0]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          linarith only [h1, h22011, h22014, h22019, h22211, h22213, hc01, hc45, hlam, hphi, ht0b, ht5b, p22534_1]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          rcases p22534_3 (m.d 0 2) (by simp) with h22549 | h22549
                                          · linarith only [h22549, hlam, p22534_0]
                                          · rcases p22534_3 (m.d 1 2) (by simp) with h22551 | h22551
                                            · linarith only [h22014, h22551, hlam]
                                            · rcases p22534_3 (m.d 2 3) (by simp) with h22553 | h22553
                                              · rcases p22534_3 (m.d 2 4) (by simp) with h22554 | h22554
                                                · linarith only [h22210, h22554, hlam]
                                                · linarith only [h19744, h22554, hlam]
                                              · linarith only [h22553, hlam, p22534_0]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          rcases p22534_3 (m.d 0 2) (by simp) with h22558 | h22558
                                          · linarith only [h22558, h4, hlam]
                                          · linarith only [h0, h22558, hlam]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          linarith only [hlam, p22534_0]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          linarith only [h19744, hc02, hc23, hlam, hphi, p22534_1]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          linarith only [h22011, h22014, h22018, h22019, h4, hlam, p22534_2]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          rcases p22534_3 (m.d 0 2) (by simp) with h22564 | h22564
                                          · linarith only [h22564, hlam, p22534_0]
                                          · rcases p22534_3 (m.d 1 2) (by simp) with h22566 | h22566
                                            · linarith only [h22016, h22566, hlam]
                                            · rcases p22534_3 (m.d 2 3) (by simp) with h22568 | h22568
                                              · rcases p22534_3 (m.d 2 4) (by simp) with h22569 | h22569
                                                · rcases p22534_3 (m.d 2 5) (by simp) with h22570 | h22570
                                                  · linarith only [h22212, h22570, hlam]
                                                  · rcases h4bigk with h22572c | h22572c | h22572c | h22572c | h22572c | h22572c | h22572c | h22572c | h22572c | h22572c | h22572c | h22572c | h22572c | h22572c | h22572c | h22572c | h22572c | h22572c | h22572c | h22572c | h22572c | h22572c | h22572c | h22572c | h22572c
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [hlam, p22572_0]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      rcases p22572_3 (m.d 0 4) (by simp) with h22574 | h22574
                                                      · rcases p22572_3 (m.d 1 4) (by simp) with h22575 | h22575
                                                        · linarith only [h2, h22575, hlam]
                                                        · rcases p22572_3 (m.d 2 4) (by simp) with h22577 | h22577
                                                          · rcases p22572_3 (m.d 3 4) (by simp) with h22578 | h22578
                                                            · linarith only [h22011, h22578, hlam]
                                                            · linarith only [h22019, h22578, hlam]
                                                          · linarith only [h22016, h22577, hlam]
                                                      · linarith only [h2, h22574, hlam]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [h19744, hlam, p22572_1]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [h19744, h22014, h22019, h22210, hc12, hc23, hlam, hphi, p22572_1]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      rcases p22572_3 (m.d 0 4) (by simp) with h22585 | h22585
                                                      · rcases p22572_3 (m.d 1 4) (by simp) with h22586 | h22586
                                                        · linarith only [h2, h22586, hlam]
                                                        · linarith only [h22209, h22586, hlam]
                                                      · linarith only [h22585, hlam, p22572_0]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [h2, hlam, p22572_0]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [hlam, p22572_0]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [h22016, hlam, p22572_1]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [h22019, hlam, p22572_1]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [hc01, hc45, hlam, hphi, ht0b, ht5b, p22214_1, p22572_1]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [h22011, h22014, h22018, h22019, h22210, h22211, h22213, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22572_1]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      rcases p22572_3 (m.d 0 4) (by simp) with h22596 | h22596
                                                      · linarith only [h19744, h22596, hlam]
                                                      · linarith only [h2, h22596, hlam]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [hlam, p22572_0]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [h22014, h22018, h22019, h22210, h22211, h22213, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22572_1]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [h0, h22018, h22211, h22213, hlam, p22534_1, p22572_2]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [h22011, hlam, p22572_0]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [h1, h22011, hlam, p22214_2, p22572_1]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [h22210, hlam, p22572_0]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [hlam, p22572_0]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      rcases p22572_3 (m.d 0 4) (by simp) with h22606 | h22606
                                                      · rcases p22572_3 (m.d 1 4) (by simp) with h22607 | h22607
                                                        · linarith only [h22019, h22607, hlam]
                                                        · linarith only [h22209, h22607, hlam]
                                                      · linarith only [h22013, h22606, hlam]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [h22013, hlam, p22572_0]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [h22209, hlam, p22572_0]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [h22212, hlam, p22572_0]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [h22213, hlam, p22572_0]
                                                    · have p22572_0 := h22572c.1
                                                      have p22572_1 := h22572c.2.1
                                                      have p22572_2 := h22572c.2.2.1
                                                      have p22572_3 := h22572c.2.2.2
                                                      linarith only [hlam, p22572_0]
                                                · linarith only [h22569, hlam, p22534_0]
                                              · linarith only [h22568, h4, hlam]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          rcases p22534_3 (m.d 0 2) (by simp) with h22618 | h22618
                                          · linarith only [h19744, h22618, hlam]
                                          · linarith only [h0, h22618, hlam]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          linarith only [h22210, hlam, p22534_0]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          linarith only [hlam, p22534_0]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          rcases p22534_3 (m.d 0 2) (by simp) with h22623 | h22623
                                          · linarith only [h19744, h22623, hlam]
                                          · linarith only [h22010, h22623, hlam]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          linarith only [h22010, hlam, p22534_0]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          linarith only [h22018, hlam, p22534_0]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          linarith only [h22211, hlam, p22534_0]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          linarith only [h22212, hlam, p22534_1]
                                        · have p22534_0 := h22534c.1
                                          have p22534_1 := h22534c.2.1
                                          have p22534_2 := h22534c.2.2.1
                                          have p22534_3 := h22534c.2.2.2
                                          linarith only [hlam, p22534_0]
                            · linarith only [h22232, hlam, p22214_0]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            rcases p22214_3 (m.d 0 1) (by simp) with h22632 | h22632
                            · rcases p22214_3 (m.d 1 2) (by simp) with h22633 | h22633
                              · linarith only [h0, h22633, hlam]
                              · linarith only [h22018, h22633, hlam]
                            · linarith only [h22632, hlam, p22214_0]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [h0, hlam, p22214_0]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [hlam, p22214_0]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [h22014, hlam, p22214_1]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [h22016, hlam, p22214_1]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [h1, h22011, h22014, h22019, hc01, hc15, hlam, hphi, ht0b, ht5b, p22214_1]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [h1, hlam, p22214_0]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [h1, h22011, h22019, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p22214_1]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [hlam, p22214_0]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [h22019, hlam, p22214_0]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [h22011, h22018, h22019, h22211, h22213, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22214_1]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [h2, hlam, p22214_0]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [h2, h22018, h22211, h22213, hc01, hc45, hlam, hphi, ht0b, ht5b, p22214_1]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [h22011, h22014, h22018, h22019, h22211, h22213, h4, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p22214_1]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [hlam, p22214_0]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            rcases p22214_3 (m.d 0 1) (by simp) with h22651 | h22651
                            · rcases p22214_3 (m.d 1 2) (by simp) with h22652 | h22652
                              · linarith only [h22016, h22652, hlam]
                              · linarith only [h22018, h22652, hlam]
                            · linarith only [h22651, h3, hlam]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [h3, hlam, p22214_0]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [h22018, hlam, p22214_0]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [h22208, hlam, p22214_0]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [h22209, hlam, p22214_0]
                          · have p22214_0 := h22214c.1
                            have p22214_1 := h22214c.2.1
                            have p22214_2 := h22214c.2.2.1
                            have p22214_3 := h22214c.2.2.2
                            linarith only [hlam, p22214_0]
                        · linarith only [h22013, h22014, h22018, h22019, h22211, h22213, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h19744, h22013, h22212, hlam]
                    · linarith only [h22011, h22014, h22019, h22211, h4, hc12, hc35, hlam, hphi, ht23]
                  · linarith only [h22011, h22210, h4, hlam]
                · linarith only [h22014, h22018, h22019, h22209, hlam]
              · linarith only [h22014, h22018, h22208, hlam]
          · linarith only [h19744, h22010, h22018, hc12, hc24, hlam, hphi]
    · linarith only [h19744, h22010, h22013, hlam]
  · linarith only [h19744, h22010, h22011, h22012, hlam]

end R2N4
