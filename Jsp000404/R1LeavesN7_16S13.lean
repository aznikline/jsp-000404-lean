import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_21_15_H_I_L_I_s10_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6137 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7252 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8021 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8693 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h10070 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h1bigk := hb1.1
  have h0 := hg0
  have h6137 := hg6137
  have h7252 := hg7252
  have h8021 := hg8021
  rcases m.htr 0 2 5 (by decide) (by decide) with h10071 | h10071
  · rcases m.htr 0 3 4 (by decide) (by decide) with h10072 | h10072
    · rcases m.htr 0 3 5 (by decide) (by decide) with h10073 | h10073
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10074 | h10074
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10075 | h10075
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10076 | h10076
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10077 | h10077
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10078 | h10078
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10079 | h10079
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10080 | h10080
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10081 | h10081
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10082 | h10082
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10083 | h10083
                          · linarith only [h10070, h10075, h10083, h8693, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h10070, h10074, h10075, h10083, h8693, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h10073, h10082, h8693, hlam]
                      · linarith only [h10072, h10081, h8693, hlam]
                    · linarith only [h10070, h10074, h10075, h10080, h8693, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · linarith only [h10070, h10073, h10074, h10075, h10079, h6137, h8693, hc01, hc12, hlam, hphi]
                · linarith only [h10070, h10072, h10075, h10078, h8693, hlam]
              · linarith only [h10071, h10075, h10077, h8693, hlam]
            · linarith only [h10070, h10075, h10076, h8693, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10093 | h10093
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10094 | h10094
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10095 | h10095
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10096 | h10096
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10097 | h10097
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10098 | h10098
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10099 | h10099
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10100 | h10100
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10101 | h10101
                            · rcases h1bigk with h10102c | h10102c | h10102c | h10102c | h10102c | h10102c | h10102c | h10102c | h10102c | h10102c | h10102c | h10102c | h10102c | h10102c | h10102c | h10102c | h10102c | h10102c | h10102c | h10102c | h10102c | h10102c | h10102c | h10102c | h10102c
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [hlam, p10102_0]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [h0, hlam, p10102_0]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [h6137, hlam, p10102_0]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [h7252, hlam, p10102_0]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [h8021, hlam, p10102_0]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [hc01, hc12, hlam, hphi, p10102_1]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [hlam, p10102_0]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [h10075, hlam, p10102_0]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [h10075, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10102_1]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [h10075, h8021, hc01, hc23, hlam, hphi, ht12, p10102_1]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [h10075, hc01, hc23, hlam, hphi, ht12, p10102_1]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [h0, h10075, hc02, hc23, hlam, hphi, p10102_1]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [hlam, p10102_0]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [h10075, h10097, h8021, hc01, hc23, hlam, hphi, ht12, p10102_1]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [h10075, h8021, hc01, hc23, hlam, hphi, ht12, p10102_1]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [hc01, hc14, hlam, hphi, p10102_1]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [h10093, hlam, p10102_1]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [h10095, hlam, p10102_0]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [hlam, p10102_0]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [h10093, h8021, hc01, hc12, hlam, hphi, p10102_1]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [hc01, hc15, hlam, hphi, p10102_1]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [h10094, hlam, p10102_1]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [h10096, hlam, p10102_0]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [h10097, hlam, p10102_0]
                              · have p10102_0 := h10102c.1
                                have p10102_1 := h10102c.2.1
                                have p10102_2 := h10102c.2.2.1
                                have p10102_3 := h10102c.2.2.2
                                linarith only [hlam, p10102_0]
                            · linarith only [h0, h10070, h10075, h10100, h10101, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10129 | h10129
                            · linarith only [h10098, h10100, h10129, hlam]
                            · rcases h1bigk with h10131c | h10131c | h10131c | h10131c | h10131c | h10131c | h10131c | h10131c | h10131c | h10131c | h10131c | h10131c | h10131c | h10131c | h10131c | h10131c | h10131c | h10131c | h10131c | h10131c | h10131c | h10131c | h10131c | h10131c | h10131c
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [hlam, p10131_0]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [h0, hlam, p10131_0]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [h6137, hlam, p10131_0]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [h7252, hlam, p10131_0]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [h8021, hlam, p10131_0]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [h10075, hc01, hc23, hlam, hphi, ht12, p10131_1]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [hlam, p10131_0]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [h10075, hlam, p10131_0]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [h10075, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10131_1]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [h10075, h8021, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10131_1]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [h10075, hc01, hc23, hlam, hphi, ht12, p10131_1]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [h0, h10075, hc02, hc23, hlam, hphi, p10131_1]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [hlam, p10131_0]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [h10074, h10075, h10098, h10100, h7252, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10131_1]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [h10075, h8021, hc01, hc23, hlam, hphi, ht12, p10131_1]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [hc01, hc14, hlam, hphi, p10131_1]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [h10093, hlam, p10131_1]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [h10095, hlam, p10131_0]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [hlam, p10131_0]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [h10093, h8021, hc01, hc12, hlam, hphi, p10131_1]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [hc01, hc15, hlam, hphi, p10131_1]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [h10094, hlam, p10131_1]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [h10096, hlam, p10131_0]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [h10097, hlam, p10131_0]
                              · have p10131_0 := h10131c.1
                                have p10131_1 := h10131c.2.1
                                have p10131_2 := h10131c.2.2.1
                                have p10131_3 := h10131c.2.2.2
                                linarith only [hlam, p10131_0]
                        · linarith only [h0, h10075, h10099, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h10075, h10093, h10097, h10098, h8021, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h10070, h10074, h10075, h10097, h7252, hc01, hc23, hlam, hphi, ht12]
                  · linarith only [h10071, h10073, h10096, h6137, h8693, hlam]
                · linarith only [h10072, h10095, h6137, hlam]
              · linarith only [h0, h10071, h10094, hlam]
            · linarith only [h0, h10070, h10093, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10164 | h10164
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10165 | h10165
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10166 | h10166
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10167 | h10167
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10168 | h10168
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10169 | h10169
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10170 | h10170
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10171 | h10171
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10172 | h10172
                          · linarith only [h10070, h10074, h10164, h10172, h8693, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10174 | h10174
                            · linarith only [h10071, h10074, h10164, h10170, h10172, h10174, h7252, h8693, hc01, hc12, hlam, hphi]
                            · rcases h1bigk with h10176c | h10176c | h10176c | h10176c | h10176c | h10176c | h10176c | h10176c | h10176c | h10176c | h10176c | h10176c | h10176c | h10176c | h10176c | h10176c | h10176c | h10176c | h10176c | h10176c | h10176c | h10176c | h10176c | h10176c | h10176c
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [hlam, p10176_0]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [h0, hlam, p10176_0]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [h6137, hlam, p10176_0]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [h7252, hlam, p10176_0]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [h8021, hlam, p10176_0]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [hc01, hc12, hlam, hphi, p10176_1]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [hlam, p10176_0]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [h10074, h10167, h10169, h7252, hc01, hc12, hlam, hphi, p10176_1]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [h10074, h10169, h7252, hc01, hc12, hlam, hphi, p10176_1]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [h10074, h10169, h7252, hc01, hc12, hlam, hphi, p10176_1]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [hc01, hc13, hlam, hphi, p10176_1]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [h10164, hlam, p10176_1]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [hlam, p10176_0]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [h10074, h10164, h10169, h7252, hc01, hc12, hlam, hphi, p10176_1]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [h10074, h10164, h10169, h7252, hc01, hc12, hlam, hphi, p10176_1]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [hc01, hc14, hlam, hphi, p10176_1]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [h10165, hlam, p10176_1]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [h10167, hlam, p10176_0]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [hlam, p10176_0]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [h10074, h10164, h10167, h10169, h7252, hc01, hc12, hlam, hphi, p10176_1]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [hc01, hc15, hlam, hphi, p10176_1]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [h10166, hlam, p10176_1]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [h10168, hlam, p10176_0]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [h10169, hlam, p10176_0]
                              · have p10176_0 := h10176c.1
                                have p10176_1 := h10176c.2.1
                                have p10176_2 := h10176c.2.2.1
                                have p10176_3 := h10176c.2.2.2
                                linarith only [hlam, p10176_0]
                        · linarith only [h10071, h10073, h10171, h8693, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h10072, h10170, h8693, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10204 | h10204
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10205 | h10205
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10206 | h10206
                          · linarith only [h10070, h10164, h10169, h10206, h8693, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10208 | h10208
                            · linarith only [h10071, h10164, h10169, h10204, h10206, h10208, h8693, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases h1bigk with h10210c | h10210c | h10210c | h10210c | h10210c | h10210c | h10210c | h10210c | h10210c | h10210c | h10210c | h10210c | h10210c | h10210c | h10210c | h10210c | h10210c | h10210c | h10210c | h10210c | h10210c | h10210c | h10210c | h10210c | h10210c
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [hlam, p10210_0]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [h0, hlam, p10210_0]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [h6137, hlam, p10210_0]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [h7252, hlam, p10210_0]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [h8021, hlam, p10210_0]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [hc01, hc12, hlam, hphi, p10210_1]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [hlam, p10210_0]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [h6137, hc01, hc12, hlam, hphi, p10210_1]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [h7252, hc01, hc12, hlam, hphi, p10210_1]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [h10169, h7252, hc01, hc12, hlam, hphi, p10210_1]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [hc01, hc13, hlam, hphi, p10210_1]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [h10164, hlam, p10210_1]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [hlam, p10210_0]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [h10164, h7252, hc01, hc12, hlam, hphi, p10210_1]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [h10164, h10169, h7252, hc01, hc12, hlam, hphi, p10210_1]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [hc01, hc14, hlam, hphi, p10210_1]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [h10165, hlam, p10210_1]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [h10167, hlam, p10210_0]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [hlam, p10210_0]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [h10169, hlam, p10210_1]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [hc01, hc15, hlam, hphi, p10210_1]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [h10166, hlam, p10210_1]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [h10168, hlam, p10210_0]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [h10169, hc14, hc45, hlam, hphi, p10210_1]
                              · have p10210_0 := h10210c.1
                                have p10210_1 := h10210c.2.1
                                have p10210_2 := h10210c.2.2.1
                                have p10210_3 := h10210c.2.2.2
                                linarith only [hlam, p10210_0]
                        · linarith only [h10073, h10205, h8693, hlam]
                      · linarith only [h10072, h10204, h8693, hlam]
                  · linarith only [h10071, h10073, h10168, h6137, h8693, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h10070, h10072, h10164, h10167, h8693, hlam]
              · linarith only [h10071, h10164, h10166, h8693, hlam]
            · linarith only [h10070, h10164, h10165, h8693, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10242 | h10242
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10243 | h10243
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10244 | h10244
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10245 | h10245
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10246 | h10246
                    · linarith only [h10074, h10164, h10242, h10246, h7252, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10248 | h10248
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10249 | h10249
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10250 | h10250
                          · linarith only [h0, h10070, h10164, h10246, h10250, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10252 | h10252
                            · linarith only [h0, h10071, h10164, h10246, h10248, h10250, h10252, h7252, hc01, hc23, hlam, hphi, ht12]
                            · rcases h1bigk with h10254c | h10254c | h10254c | h10254c | h10254c | h10254c | h10254c | h10254c | h10254c | h10254c | h10254c | h10254c | h10254c | h10254c | h10254c | h10254c | h10254c | h10254c | h10254c | h10254c | h10254c | h10254c | h10254c | h10254c | h10254c
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [hlam, p10254_0]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [h0, hlam, p10254_0]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [h6137, hlam, p10254_0]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [h7252, hlam, p10254_0]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [h8021, hlam, p10254_0]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [h10164, hc01, hc23, hlam, hphi, ht12, p10254_1]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [hlam, p10254_0]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [h10164, hlam, p10254_0]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [h10164, h7252, hc01, hc23, hlam, hphi, ht12, p10254_1]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [h10164, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10254_1]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [h10164, hc01, hc23, hlam, hphi, ht12, p10254_1]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [h0, h10164, hc02, hc23, hlam, hphi, p10254_1]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [hlam, p10254_0]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [h10164, h7252, hc01, hc23, hlam, hphi, ht12, p10254_1]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [h10164, h8021, hc01, hc23, hlam, hphi, ht12, p10254_1]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [h10242, hc01, hc12, hlam, hphi, p10254_1]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [h10242, hlam, p10254_1]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [h10244, hlam, p10254_0]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [hlam, p10254_0]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [h10246, hlam, p10254_1]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [hc01, hc15, hlam, hphi, p10254_1]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [h10243, hlam, p10254_1]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [h10245, hlam, p10254_0]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [h10164, h10243, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10254_1]
                              · have p10254_0 := h10254c.1
                                have p10254_1 := h10254c.2.1
                                have p10254_2 := h10254c.2.2.1
                                have p10254_3 := h10254c.2.2.2
                                linarith only [hlam, p10254_0]
                        · linarith only [h0, h10164, h10249, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h10164, h10243, h10246, h10248, h7252, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h10071, h10073, h10164, h10245, h6137, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h10070, h10072, h10244, h6137, h8693, hlam]
              · linarith only [h0, h10071, h10243, h6137, h8693, hc01, hc13, hlam, hphi]
            · linarith only [h0, h10070, h10242, hlam]
      · linarith only [h10071, h10073, h8693, hlam]
    · linarith only [h10070, h10072, h8693, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h10288 | h10288
    · rcases m.htr 0 3 5 (by decide) (by decide) with h10289 | h10289
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10290 | h10290
        · linarith only [h10070, h10071, h10290, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10292 | h10292
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10293 | h10293
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10294 | h10294
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10295 | h10295
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10296 | h10296
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10297 | h10297
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10298 | h10298
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10299 | h10299
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10300 | h10300
                          · linarith only [h10070, h10071, h10290, h10292, h10299, h10300, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10302 | h10302
                            · linarith only [h10070, h10071, h10298, h10300, h10302, hlam]
                            · rcases h1bigk with h10304c | h10304c | h10304c | h10304c | h10304c | h10304c | h10304c | h10304c | h10304c | h10304c | h10304c | h10304c | h10304c | h10304c | h10304c | h10304c | h10304c | h10304c | h10304c | h10304c | h10304c | h10304c | h10304c | h10304c | h10304c
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [hlam, p10304_0]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [h0, hlam, p10304_0]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [h6137, hlam, p10304_0]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [h7252, hlam, p10304_0]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [h8021, hlam, p10304_0]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [hc01, hc12, hlam, hphi, p10304_1]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [hlam, p10304_0]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [h10071, h10295, h10297, h10300, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10304_1]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [h10070, h10071, h10297, h10298, h10300, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10304_1]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [h10070, h10071, h10297, h10298, h10300, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10304_1]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [hc01, hc13, hlam, hphi, p10304_1]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [h10292, hlam, p10304_1]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [hlam, p10304_0]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [h10070, h10071, h10292, h10297, h10298, h10300, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10304_1]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [h10070, h10071, h10292, h10297, h10298, h10300, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10304_1]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [hc01, hc14, hlam, hphi, p10304_1]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [h10293, hlam, p10304_1]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [h10295, hlam, p10304_0]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [hlam, p10304_0]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [h10070, h10071, h10292, h10295, h10297, h10298, h10300, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10304_1]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [hc01, hc15, hlam, hphi, p10304_1]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [h10294, hlam, p10304_1]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [h10296, hlam, p10304_0]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [h10297, hlam, p10304_0]
                              · have p10304_0 := h10304c.1
                                have p10304_1 := h10304c.2.1
                                have p10304_2 := h10304c.2.2.1
                                have p10304_3 := h10304c.2.2.2
                                linarith only [hlam, p10304_0]
                        · linarith only [h10070, h10289, h10298, h10299, h8693, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b]
                      · linarith only [h10288, h10298, h8693, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10332 | h10332
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10333 | h10333
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10334 | h10334
                          · linarith only [h10070, h10071, h10297, h10334, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10336 | h10336
                            · linarith only [h10070, h10071, h10288, h10294, h10297, h10336, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                            · rcases h1bigk with h10338c | h10338c | h10338c | h10338c | h10338c | h10338c | h10338c | h10338c | h10338c | h10338c | h10338c | h10338c | h10338c | h10338c | h10338c | h10338c | h10338c | h10338c | h10338c | h10338c | h10338c | h10338c | h10338c | h10338c | h10338c
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [hlam, p10338_0]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [h0, hlam, p10338_0]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [h6137, hlam, p10338_0]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [h7252, hlam, p10338_0]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [h8021, hlam, p10338_0]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [hc01, hc12, hlam, hphi, p10338_1]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [hlam, p10338_0]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [h6137, hc01, hc12, hlam, hphi, p10338_1]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [h7252, hc01, hc12, hlam, hphi, p10338_1]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [h10070, h10071, h10294, h10332, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10338_1]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [hc01, hc13, hlam, hphi, p10338_1]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [h10292, hlam, p10338_1]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [hlam, p10338_0]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [h10292, h7252, hc01, hc12, hlam, hphi, p10338_1]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [h10070, h10071, h10292, h10294, h10332, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10338_1]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [hc01, hc14, hlam, hphi, p10338_1]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [h10293, hlam, p10338_1]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [h10295, hlam, p10338_0]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [hlam, p10338_0]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [h10297, hlam, p10338_1]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [hc01, hc15, hlam, hphi, p10338_1]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [h10294, hlam, p10338_1]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [h10296, hlam, p10338_0]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [h10297, hc14, hc45, hlam, hphi, p10338_1]
                              · have p10338_0 := h10338c.1
                                have p10338_1 := h10338c.2.1
                                have p10338_2 := h10338c.2.2.1
                                have p10338_3 := h10338c.2.2.2
                                linarith only [hlam, p10338_0]
                        · linarith only [h10070, h10289, h10297, h10332, h10333, h8021, h8693, hc34, hc45, hlam, hphi]
                      · linarith only [h10070, h10288, h10332, h8693, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h10289, h10292, h10296, h6137, h8693, hc01, hc12, hlam, hphi]
                · linarith only [h10288, h10292, h10295, h8693, hlam]
              · linarith only [h10070, h10292, h10294, h8693, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h10070, h10292, h10293, h8693, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10370 | h10370
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10371 | h10371
              · linarith only [h10070, h10071, h10292, h10371, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10373 | h10373
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10374 | h10374
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10375 | h10375
                    · linarith only [h10290, h10292, h10370, h10375, h7252, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10377 | h10377
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10378 | h10378
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10379 | h10379
                          · linarith only [h0, h10070, h10371, h10375, h10378, h10379, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10381 | h10381
                            · linarith only [h0, h10371, h10379, h10381, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h1bigk with h10383c | h10383c | h10383c | h10383c | h10383c | h10383c | h10383c | h10383c | h10383c | h10383c | h10383c | h10383c | h10383c | h10383c | h10383c | h10383c | h10383c | h10383c | h10383c | h10383c | h10383c | h10383c | h10383c | h10383c | h10383c
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [hlam, p10383_0]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [h0, hlam, p10383_0]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [h6137, hlam, p10383_0]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [h7252, hlam, p10383_0]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [h8021, hlam, p10383_0]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [hc01, hc12, hlam, hphi, p10383_1]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [hlam, p10383_0]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [h10292, hlam, p10383_0]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [h10371, h10378, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10383_1]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [h10371, hlam, p10383_0]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [hc01, hc13, hlam, hphi, p10383_1]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [h0, h10292, hc02, hc23, hlam, hphi, p10383_1]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [hlam, p10383_0]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [h10292, h7252, hc01, hc23, hlam, hphi, ht12, p10383_1]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [h10292, h10370, h10371, h7252, hc01, hc23, hlam, hphi, ht12, p10383_1]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [h10370, hc01, hc12, hlam, hphi, p10383_1]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [h10370, hlam, p10383_1]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [h10373, hlam, p10383_0]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [hlam, p10383_0]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [h10375, hlam, p10383_1]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [hc01, hc15, hlam, hphi, p10383_1]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [h10371, h10379, hc12, hc45, hlam, hphi, ht23, ht34, p10383_1]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [h10374, hlam, p10383_0]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [h10371, h10379, h7252, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10383_1]
                              · have p10383_0 := h10383c.1
                                have p10383_1 := h10383c.2.1
                                have p10383_2 := h10383c.2.2.1
                                have p10383_3 := h10383c.2.2.2
                                linarith only [hlam, p10383_0]
                        · linarith only [h10289, h10292, h10378, h6137, hlam]
                      · linarith only [h10292, h10370, h10377, h7252, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h10289, h10374, h6137, hlam]
                · linarith only [h10288, h10292, h10370, h10373, h6137, h7252, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h10070, h10370, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10414 | h10414
        · linarith only [h10070, h10071, h10414, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10416 | h10416
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10417 | h10417
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10418 | h10418
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10419 | h10419
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10420 | h10420
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10421 | h10421
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10422 | h10422
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10423 | h10423
                        · linarith only [h10070, h10289, h10416, h10422, h10423, h8693, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h10070, h10416, h10420, h10422, h10423, h8693, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h10288, h10422, h8693, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10427 | h10427
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10428 | h10428
                        · linarith only [h10289, h10416, h10428, h6137, hc01, hc12, hlam, hphi]
                        · linarith only [h10070, h10416, h10420, h10427, h10428, h8693, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h10288, h10427, h8693, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10432 | h10432
                    · linarith only [h10414, h10419, h10420, h10432, h7252, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10434 | h10434
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10435 | h10435
                        · linarith only [h10416, h10420, h10435, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10437 | h10437
                          · linarith only [h10070, h10416, h10420, h10432, h10437, h8693, hc15, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10439 | h10439
                            · linarith only [h10070, h10416, h10420, h10432, h10434, h10439, h7252, h8693, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h10070, h10416, h10420, h10434, h10439, h8693, hc34, hc45, hlam, hphi]
                      · linarith only [h10070, h10288, h10434, h8693, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h10070, h10288, h10416, h10419, h8693, hlam]
              · linarith only [h10070, h10416, h10418, h8693, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h10070, h10416, h10417, h8693, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10446 | h10446
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10447 | h10447
              · linarith only [h10070, h10071, h10416, h10447, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10449 | h10449
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10450 | h10450
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10451 | h10451
                    · linarith only [h10414, h10416, h10446, h10451, h7252, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10453 | h10453
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10454 | h10454
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10455 | h10455
                          · linarith only [h0, h10070, h10447, h10451, h10454, h10455, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10457 | h10457
                            · linarith only [h10070, h10289, h10416, h10447, h10450, h10453, h10455, h10457, h8693, hc12, hc23, hlam, hphi]
                            · rcases h1bigk with h10459c | h10459c | h10459c | h10459c | h10459c | h10459c | h10459c | h10459c | h10459c | h10459c | h10459c | h10459c | h10459c | h10459c | h10459c | h10459c | h10459c | h10459c | h10459c | h10459c | h10459c | h10459c | h10459c | h10459c | h10459c
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [hlam, p10459_0]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [h0, hlam, p10459_0]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [h6137, hlam, p10459_0]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [h7252, hlam, p10459_0]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [h8021, hlam, p10459_0]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [hc01, hc12, hlam, hphi, p10459_1]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [hlam, p10459_0]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [h10416, hlam, p10459_0]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [h10070, h10289, h10416, h10447, h10450, h10453, h10455, h7252, h8693, hc01, hc23, hc34, hc45, hlam, hphi, ht12, p10459_1]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [h10447, hlam, p10459_0]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [h10416, hc01, hc23, hlam, hphi, ht12, p10459_1]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [h10416, hc12, hc23, hlam, hphi, p10459_1]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [hlam, p10459_0]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [h10416, h7252, hc01, hc23, hlam, hphi, ht12, p10459_1]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [h10070, h10289, h10416, h10450, h10453, h8693, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10459_1]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [h10446, hc01, hc12, hlam, hphi, p10459_1]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [h10446, hlam, p10459_1]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [h10449, hlam, p10459_0]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [hlam, p10459_0]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [h10451, hlam, p10459_1]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [hc01, hc15, hlam, hphi, p10459_1]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [h10447, h10455, hc12, hc45, hlam, hphi, ht23, ht34, p10459_1]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [h10450, hlam, p10459_0]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [h10070, h10289, h10416, h10447, h10450, h10453, h10455, h7252, h8693, hc01, hc23, hc34, hc45, hlam, hphi, ht12, p10459_1]
                              · have p10459_0 := h10459c.1
                                have p10459_1 := h10459c.2.1
                                have p10459_2 := h10459c.2.2.1
                                have p10459_3 := h10459c.2.2.2
                                linarith only [hlam, p10459_0]
                        · linarith only [h10416, h10450, h10454, hlam]
                      · linarith only [h10070, h10289, h10416, h10450, h10453, h8693, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10487 | h10487
                    · linarith only [h10414, h10416, h10446, h10487, h7252, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10489 | h10489
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10490 | h10490
                        · linarith only [h0, h10416, h10450, h10490, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h10416, h10446, h10490, h7252, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h10416, h10446, h10489, h7252, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h10288, h10449, h6137, hlam]
            · linarith only [h0, h10070, h10446, hlam]
    · linarith only [h10070, h10288, h8693, hlam]

set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_21_15_H_I_L_I_s10_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6137 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7252 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8021 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8693 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h10070 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h10497 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h1bigk := hb1.1
  have h0 := hg0
  have h6137 := hg6137
  have h7252 := hg7252
  have h8021 := hg8021
  rcases m.htr 0 3 4 (by decide) (by decide) with h10498 | h10498
  · rcases m.htr 0 3 5 (by decide) (by decide) with h10499 | h10499
    · rcases m.htr 0 4 5 (by decide) (by decide) with h10500 | h10500
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10501 | h10501
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10502 | h10502
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10503 | h10503
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10504 | h10504
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10505 | h10505
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10506 | h10506
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10507 | h10507
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10508 | h10508
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10509 | h10509
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10510 | h10510
                          · rcases h1bigk with h10511c | h10511c | h10511c | h10511c | h10511c | h10511c | h10511c | h10511c | h10511c | h10511c | h10511c | h10511c | h10511c | h10511c | h10511c | h10511c | h10511c | h10511c | h10511c | h10511c | h10511c | h10511c | h10511c | h10511c | h10511c
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [hlam, p10511_0]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [h0, hlam, p10511_0]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [h6137, hlam, p10511_0]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [h7252, hlam, p10511_0]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [h8021, hlam, p10511_0]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p10511_1]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [hlam, p10511_0]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [h10070, h10502, h10504, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10511_1]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [h10070, h10497, h10502, h10508, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10511_1]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [h8021, hc01, hc12, hlam, hphi, p10511_1]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [hc01, hc13, hlam, hphi, p10511_1]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [h10501, hlam, p10511_1]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [hlam, p10511_0]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [h10070, h10497, h10501, h10502, h10508, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10511_1]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [h10501, h8021, hc01, hc12, hlam, hphi, p10511_1]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p10511_1]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [h10502, hlam, p10511_1]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [h10504, hlam, p10511_0]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [hlam, p10511_0]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [h10501, h10504, h8021, hc01, hc12, hlam, hphi, p10511_1]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p10511_1]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [h10503, hlam, p10511_1]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [h10505, hlam, p10511_0]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [h10506, hlam, p10511_0]
                            · have p10511_0 := h10511c.1
                              have p10511_1 := h10511c.2.1
                              have p10511_2 := h10511c.2.2.1
                              have p10511_3 := h10511c.2.2.2
                              linarith only [hlam, p10511_0]
                          · linarith only [h10497, h10501, h10509, h10510, h8693, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h10070, h10497, h10498, h10500, h10509, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h10499, h10508, h8693, hlam]
                    · linarith only [h10498, h10507, h8693, hlam]
                  · linarith only [h10070, h10497, h10500, h10506, h7252, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h10497, h10499, h10501, h10505, h6137, h8693, hc01, hc12, hlam, hphi]
              · linarith only [h10498, h10501, h10504, h8693, hlam]
            · linarith only [h10501, h10503, h8693, hc02, hc25, hlam, hphi]
          · linarith only [h10497, h10501, h10502, h8021, h8693, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10546 | h10546
          · linarith only [h10070, h10501, h10546, hc02, hc23, hlam, hphi]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10548 | h10548
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10549 | h10549
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10550 | h10550
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10551 | h10551
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10552 | h10552
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10553 | h10553
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10554 | h10554
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10555 | h10555
                          · rcases h1bigk with h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c | h10556c
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [hlam, p10556_0]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [h0, hlam, p10556_0]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [h6137, hlam, p10556_0]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [h7252, hlam, p10556_0]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [h8021, hlam, p10556_0]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [h10546, h10552, hc01, hc23, hlam, hphi, ht12, p10556_1]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [hlam, p10556_0]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [h10501, hlam, p10556_0]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [h10546, hlam, p10556_0]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [h10546, h10552, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10556_1]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [h10501, hc01, hc23, hlam, hphi, ht12, p10556_1]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [h10501, hc12, hc23, hlam, hphi, p10556_1]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [hlam, p10556_0]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [h10501, h7252, hc01, hc23, hlam, hphi, ht12, p10556_1]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [h10501, h8021, hc01, hc23, hlam, hphi, ht12, p10556_1]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p10556_1]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [h10546, h10548, h10552, h8021, hc01, hc23, hlam, hphi, ht12, p10556_1]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [h10549, hlam, p10556_0]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [hlam, p10556_0]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [h10546, h10552, h8021, hc01, hc23, hlam, hphi, ht12, p10556_1]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [h10548, hc01, hc12, hlam, hphi, p10556_1]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [h10548, hlam, p10556_1]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [h10550, hlam, p10556_0]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [h10551, hlam, p10556_0]
                            · have p10556_0 := h10556c.1
                              have p10556_1 := h10556c.2.1
                              have p10556_2 := h10556c.2.2.1
                              have p10556_3 := h10556c.2.2.2
                              linarith only [hlam, p10556_0]
                          · rcases h1bigk with h10582c | h10582c | h10582c | h10582c | h10582c | h10582c | h10582c | h10582c | h10582c | h10582c | h10582c | h10582c | h10582c | h10582c | h10582c | h10582c | h10582c | h10582c | h10582c | h10582c | h10582c | h10582c | h10582c | h10582c | h10582c
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [hlam, p10582_0]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [h0, hlam, p10582_0]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [h6137, hlam, p10582_0]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [h7252, hlam, p10582_0]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [h8021, hlam, p10582_0]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [h10546, h10552, hc01, hc23, hlam, hphi, ht12, p10582_1]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [hlam, p10582_0]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [h10501, hlam, p10582_0]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [h10546, hlam, p10582_0]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [h10546, h10552, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10582_1]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [h10501, hc01, hc23, hlam, hphi, ht12, p10582_1]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [h10501, hc12, hc23, hlam, hphi, p10582_1]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [hlam, p10582_0]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [h10501, h7252, hc01, hc23, hlam, hphi, ht12, p10582_1]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [h10501, h8021, hc01, hc23, hlam, hphi, ht12, p10582_1]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p10582_1]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [h0, h10546, h10552, hc02, hc23, hlam, hphi, p10582_1]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [h10549, hlam, p10582_0]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [hlam, p10582_0]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [h10546, h10552, h8021, hc01, hc23, hlam, hphi, ht12, p10582_1]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [h10548, hc01, hc12, hlam, hphi, p10582_1]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [h10548, hlam, p10582_1]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [h10550, hlam, p10582_0]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [h10551, hlam, p10582_0]
                            · have p10582_0 := h10582c.1
                              have p10582_1 := h10582c.2.1
                              have p10582_2 := h10582c.2.2.1
                              have p10582_3 := h10582c.2.2.2
                              linarith only [hlam, p10582_0]
                        · linarith only [h0, h10546, h10554, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h10546, h10548, h10552, h10553, h8021, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h10498, h10501, h10552, h6137, hlam]
                  · linarith only [h10498, h10500, h10551, h6137, h7252, hc01, hc13, hlam, hphi]
                · linarith only [h10497, h10499, h10550, h6137, h8693, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h10498, h10549, h6137, hlam]
            · linarith only [h0, h10497, h10548, hlam]
      · linarith only [h10070, h10497, h10500, hlam]
    · linarith only [h10070, h10497, h10498, h10499, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h10617 | h10617
    · rcases m.htr 0 4 5 (by decide) (by decide) with h10618 | h10618
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10619 | h10619
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10620 | h10620
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10621 | h10621
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10622 | h10622
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10623 | h10623
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10624 | h10624
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10625 | h10625
                    · linarith only [h10497, h10498, h10619, h10625, h8693, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h10497, h10619, h10622, h10625, h8693, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h10618, h10624, h7252, hlam]
                · linarith only [h10617, h10623, h6137, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10630 | h10630
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10631 | h10631
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10632 | h10632
                    · linarith only [h10619, h10622, h10632, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10634 | h10634
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10635 | h10635
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10636 | h10636
                          · rcases h1bigk with h10637c | h10637c | h10637c | h10637c | h10637c | h10637c | h10637c | h10637c | h10637c | h10637c | h10637c | h10637c | h10637c | h10637c | h10637c | h10637c | h10637c | h10637c | h10637c | h10637c | h10637c | h10637c | h10637c | h10637c | h10637c
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [hlam, p10637_0]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [h0, hlam, p10637_0]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [h6137, hlam, p10637_0]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [h7252, hlam, p10637_0]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [h8021, hlam, p10637_0]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [hc01, hc12, hlam, hphi, p10637_1]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [hlam, p10637_0]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [h6137, hc01, hc12, hlam, hphi, p10637_1]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [h10070, h10498, h10620, h6137, hc01, hc12, hlam, hphi, p10637_1]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [h8021, hc01, hc12, hlam, hphi, p10637_1]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [h10622, hc01, hc34, hlam, hphi, ht12, ht23, p10637_1]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [h10619, hlam, p10637_1]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [hlam, p10637_0]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [h10622, hlam, p10637_1]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [h8021, hc01, hc13, hlam, hphi, p10637_1]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p10637_1]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [h10620, hlam, p10637_1]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [h6137, hc01, hc14, hlam, hphi, p10637_1]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [hlam, p10637_0]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [h10622, h8021, hc01, hc34, hlam, hphi, ht12, ht23, p10637_1]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [hc01, hc15, hlam, hphi, p10637_1]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [h10621, hlam, p10637_1]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [h10630, hlam, p10637_0]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [h10631, hlam, p10637_0]
                            · have p10637_0 := h10637c.1
                              have p10637_1 := h10637c.2.1
                              have p10637_2 := h10637c.2.2.1
                              have p10637_3 := h10637c.2.2.2
                              linarith only [hlam, p10637_0]
                          · linarith only [h10622, h10636, h6137, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h10497, h10618, h10632, h10635, h8693, hc04, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h10497, h10617, h10634, h8693, hc03, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h10497, h10618, h10619, h10622, h10631, h7252, h8693, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h10497, h10617, h10619, h10630, h8693, hlam]
            · linarith only [h10070, h10497, h10619, h10620, h10621, h8693, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
          · linarith only [h10619, h10620, h8693, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10670 | h10670
          · linarith only [h10070, h10497, h10619, h10670, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10672 | h10672
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10673 | h10673
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10674 | h10674
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10675 | h10675
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10676 | h10676
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10677 | h10677
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10678 | h10678
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10679 | h10679
                          · rcases h1bigk with h10680c | h10680c | h10680c | h10680c | h10680c | h10680c | h10680c | h10680c | h10680c | h10680c | h10680c | h10680c | h10680c | h10680c | h10680c | h10680c | h10680c | h10680c | h10680c | h10680c | h10680c | h10680c | h10680c | h10680c | h10680c
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [hlam, p10680_0]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [h0, hlam, p10680_0]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [h6137, hlam, p10680_0]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [h7252, hlam, p10680_0]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [h8021, hlam, p10680_0]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [h10670, h10676, hc01, hc23, hlam, hphi, ht12, p10680_1]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [hlam, p10680_0]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [h10619, hlam, p10680_0]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [h10670, hlam, p10680_0]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [h10670, h10676, h8021, hc01, hc23, hlam, hphi, ht12, p10680_1]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [h10619, hc01, hc23, hlam, hphi, ht12, p10680_1]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [h10619, hc12, hc23, hlam, hphi, p10680_1]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [hlam, p10680_0]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [h10619, h7252, hc01, hc23, hlam, hphi, ht12, p10680_1]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [h10619, h8021, hc01, hc23, hlam, hphi, ht12, p10680_1]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [hc01, hc14, hlam, hphi, p10680_1]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [h10670, h10672, h10676, h8021, hc01, hc23, hlam, hphi, ht12, p10680_1]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [h10673, hlam, p10680_0]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [hlam, p10680_0]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [h10670, h10676, h8021, hc01, hc23, hlam, hphi, ht12, p10680_1]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [h10672, hc01, hc12, hlam, hphi, p10680_1]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [h10672, hlam, p10680_1]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [h10674, hlam, p10680_0]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [h10675, hlam, p10680_0]
                            · have p10680_0 := h10680c.1
                              have p10680_1 := h10680c.2.1
                              have p10680_2 := h10680c.2.2.1
                              have p10680_3 := h10680c.2.2.2
                              linarith only [hlam, p10680_0]
                          · linarith only [h10498, h10618, h10679, hlam]
                        · linarith only [h10497, h10498, h10618, h10670, h10678, h8693, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h10498, h10619, h10673, h10677, h8693, hc02, hc35, hlam, hphi, ht23]
                    · linarith only [h10619, h10673, h10676, hlam]
                  · linarith only [h10497, h10498, h10618, h10619, h10673, h10675, h7252, h8693, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h10498, h10617, h10673, h10674, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10712 | h10712
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10713 | h10713
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10714 | h10714
                    · linarith only [h10619, h10672, h10673, h10714, h8021, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h10619, h10672, h10714, h8021, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h10497, h10618, h10619, h10713, h7252, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h10617, h10712, h6137, hlam]
            · linarith only [h0, h10497, h10672, hlam]
      · linarith only [h10497, h10498, h10618, h8693, hlam]
    · linarith only [h10497, h10617, h8693, hlam]

end R2N4
