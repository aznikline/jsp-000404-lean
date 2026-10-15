import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6253 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7338 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8081 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8735 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h10112 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h6253 := hg6253
  have h7338 := hg7338
  have h8081 := hg8081
  rcases m.htr 0 2 5 (by decide) (by decide) with h10113 | h10113
  · rcases m.htr 0 3 4 (by decide) (by decide) with h10114 | h10114
    · rcases m.htr 0 3 5 (by decide) (by decide) with h10115 | h10115
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10116 | h10116
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10117 | h10117
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10118 | h10118
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10119 | h10119
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10120 | h10120
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10121 | h10121
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10122 | h10122
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10123 | h10123
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10124 | h10124
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10125 | h10125
                          · linarith only [h10112, h10117, h10125, h8735, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h10112, h10116, h10117, h10125, h8735, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h10113, h10115, h10124, h8735, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h10114, h10123, h8735, hlam]
                    · linarith only [h0, h10112, h10116, h10122, h7338, hc01, hc12, hlam, hphi]
                  · linarith only [h10112, h10115, h10116, h10117, h10121, h6253, h8735, hc01, hc12, hlam, hphi]
                · linarith only [h10112, h10114, h10117, h10120, h8735, hlam]
              · linarith only [h10117, h10119, h8735, hc02, hc25, hlam, hphi]
            · linarith only [h10112, h10117, h10118, h8735, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10135 | h10135
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10136 | h10136
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10137 | h10137
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10138 | h10138
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10139 | h10139
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10140 | h10140
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10141 | h10141
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10142 | h10142
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10143 | h10143
                            · rcases h0bigk with h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c | h10144c
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [hlam, p10144_0]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h0, hlam, p10144_1]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h6253, hlam, p10144_0]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h7338, hlam, p10144_1]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h8081, hlam, p10144_1]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p10144_1]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [hlam, p10144_0]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h8735, hlam, p10144_0]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h0, h10117, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10144_1]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h0, h10117, h8081, hc01, hc23, hlam, hphi, ht12, p10144_1]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h8735, hc01, hc23, hlam, hphi, ht12, p10144_1]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h8735, hc02, hc23, hlam, hphi, p10144_1]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [hlam, p10144_0]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h10112, h10140, h10143, h8735, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10144_1]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h8081, h8735, hc01, hc23, hlam, hphi, ht12, p10144_1]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h10117, h10135, h7338, hc01, hc23, hlam, hphi, ht12, p10144_1]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h10112, hlam, p10144_0]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h10114, hlam, p10144_0]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [hlam, p10144_0]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h10117, h10135, h7338, h8081, hc01, hc23, hlam, hphi, ht12, p10144_1]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h10117, h10135, h10139, h8081, hc01, hc23, hlam, hphi, ht12, p10144_1]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h10113, hlam, p10144_1]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h10115, hlam, p10144_0]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [h10116, hlam, p10144_1]
                              · have p10144_0 := h10144c.1
                                have p10144_1 := h10144c.2.1
                                have p10144_2 := h10144c.2.2.1
                                have p10144_3 := h10144c.2.2.2
                                linarith only [hlam, p10144_0]
                            · linarith only [h0, h10112, h10117, h10142, h10143, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10171 | h10171
                            · linarith only [h10140, h10142, h10171, hlam]
                            · rcases h0bigk with h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c | h10173c
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [hlam, p10173_0]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h0, hlam, p10173_1]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h6253, hlam, p10173_0]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h7338, hlam, p10173_1]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h8081, hlam, p10173_1]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h0, h10117, hc01, hc23, hlam, hphi, ht12, p10173_1]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [hlam, p10173_0]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h8735, hlam, p10173_0]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h0, h10117, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10173_1]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h0, h10117, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10173_1]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h10117, h6253, hc01, hc23, hlam, hphi, ht12, p10173_1]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h10117, h6253, hc02, hc23, hlam, hphi, p10173_1]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [hlam, p10173_0]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h10117, h6253, h7338, hc01, hc23, hlam, hphi, ht12, p10173_1]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h10117, h6253, h8081, hc01, hc23, hlam, hphi, ht12, p10173_1]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h10117, h10135, h7338, hc01, hc23, hlam, hphi, ht12, p10173_1]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h10112, hlam, p10173_0]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h10114, hlam, p10173_0]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [hlam, p10173_0]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h0, h10112, h10117, h8081, hc01, hc23, hlam, hphi, ht12, p10173_1]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h10117, h10135, h10139, h8081, hc01, hc23, hlam, hphi, ht12, p10173_1]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h10113, hlam, p10173_1]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h10115, hlam, p10173_0]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [h10116, hlam, p10173_1]
                              · have p10173_0 := h10173c.1
                                have p10173_1 := h10173c.2.1
                                have p10173_2 := h10173c.2.2.1
                                have p10173_3 := h10173c.2.2.2
                                linarith only [hlam, p10173_0]
                        · linarith only [h0, h10117, h10141, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h10117, h10140, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h10116, h10139, h7338, hlam]
                  · linarith only [h10113, h10115, h10138, h6253, h8735, hlam]
                · linarith only [h10114, h10137, h6253, hlam]
              · linarith only [h0, h10113, h10136, hlam]
            · linarith only [h0, h10112, h10135, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10206 | h10206
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10207 | h10207
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10208 | h10208
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10209 | h10209
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10210 | h10210
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10211 | h10211
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10212 | h10212
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10213 | h10213
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10214 | h10214
                          · linarith only [h10112, h10116, h10206, h10214, h8735, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10216 | h10216
                            · linarith only [h10113, h10116, h10206, h10212, h10214, h10216, h7338, h8735, hc01, hc12, hlam, hphi]
                            · rcases h0bigk with h10218c | h10218c | h10218c | h10218c | h10218c | h10218c | h10218c | h10218c | h10218c | h10218c | h10218c | h10218c | h10218c | h10218c | h10218c | h10218c | h10218c | h10218c | h10218c | h10218c | h10218c | h10218c | h10218c | h10218c | h10218c
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [hlam, p10218_0]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h0, hlam, p10218_1]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h6253, hlam, p10218_0]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h7338, hlam, p10218_1]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h8081, hlam, p10218_1]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h10206, h8735, hc01, hc12, hlam, hphi, p10218_1]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [hlam, p10218_0]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h8735, hlam, p10218_0]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h10206, h7338, h8735, hc01, hc12, hlam, hphi, p10218_1]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h10206, h8735, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10218_1]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h6253, hc01, hc13, hlam, hphi, p10218_1]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h10206, h8735, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10218_1]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [hlam, p10218_0]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h10206, h7338, h8735, hc01, hc12, hlam, hphi, p10218_1]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h10206, h8081, h8735, hc01, hc12, hlam, hphi, p10218_1]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h10116, h10211, hc01, hc14, hlam, hphi, p10218_1]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h10112, hlam, p10218_0]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h10114, hlam, p10218_0]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [hlam, p10218_0]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h10116, hlam, p10218_0]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h8081, hc01, hc15, hlam, hphi, p10218_1]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h10113, hlam, p10218_1]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h10115, hlam, p10218_0]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [h0, h10113, h7338, hc01, hc12, hlam, hphi, p10218_1]
                              · have p10218_0 := h10218c.1
                                have p10218_1 := h10218c.2.1
                                have p10218_2 := h10218c.2.2.1
                                have p10218_3 := h10218c.2.2.2
                                linarith only [hlam, p10218_0]
                        · linarith only [h10115, h10213, h8735, hlam]
                      · linarith only [h10114, h10212, h8735, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10246 | h10246
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10247 | h10247
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10248 | h10248
                          · linarith only [h10112, h10211, h10248, h8735, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10250 | h10250
                            · linarith only [h10211, h10250, h7338, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h0bigk with h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c | h10252c
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h0, hlam, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h6253, hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h7338, hlam, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h8081, hlam, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10206, h8735, hc01, hc12, hlam, hphi, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h8735, hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10206, h7338, h8735, hc01, hc12, hlam, hphi, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10116, h10206, h7338, h8735, hc01, hc12, hlam, hphi, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10206, h8735, hc01, hc12, hlam, hphi, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10206, h8735, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10206, h7338, h8735, hc01, hc12, hlam, hphi, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10116, h10206, h7338, h8735, hc01, hc12, hlam, hphi, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h7338, hc01, hc14, hlam, hphi, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10112, hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10114, hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10116, hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h8081, hc01, hc15, hlam, hphi, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10113, hlam, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10115, hlam, p10252_0]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [h10113, h10206, h8735, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p10252_1]
                              · have p10252_0 := h10252c.1
                                have p10252_1 := h10252c.2.1
                                have p10252_2 := h10252c.2.2.1
                                have p10252_3 := h10252c.2.2.2
                                linarith only [hlam, p10252_0]
                        · linarith only [h10115, h10247, h8735, hlam]
                      · linarith only [h10114, h10246, h8735, hlam]
                  · linarith only [h10113, h10115, h10210, h6253, h8735, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h10112, h10114, h10209, h6253, h8735, hlam]
              · linarith only [h10113, h10208, h8735, hc12, hc23, hlam, hphi]
            · linarith only [h10112, h10206, h10207, h8735, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10284 | h10284
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10285 | h10285
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10286 | h10286
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10287 | h10287
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10288 | h10288
                    · linarith only [h10116, h10206, h10284, h10288, h7338, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10290 | h10290
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10291 | h10291
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10292 | h10292
                          · linarith only [h0, h10112, h10206, h10288, h10292, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10294 | h10294
                            · linarith only [h10288, h10290, h10294, h7338, hc01, hc24, hlam, hphi, ht12]
                            · rcases h0bigk with h10296c | h10296c | h10296c | h10296c | h10296c | h10296c | h10296c | h10296c | h10296c | h10296c | h10296c | h10296c | h10296c | h10296c | h10296c | h10296c | h10296c | h10296c | h10296c | h10296c | h10296c | h10296c | h10296c | h10296c | h10296c
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [hlam, p10296_0]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h0, hlam, p10296_1]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h6253, hlam, p10296_0]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h7338, hlam, p10296_1]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h8081, hlam, p10296_1]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h0, h10206, hc01, hc23, hlam, hphi, ht12, p10296_1]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [hlam, p10296_0]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h8735, hlam, p10296_0]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h0, h10206, h7338, hc01, hc23, hlam, hphi, ht12, p10296_1]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h0, h10116, h10206, h7338, hc01, hc23, hlam, hphi, ht12, p10296_1]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h10206, h6253, hc01, hc23, hlam, hphi, ht12, p10296_1]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h10206, h6253, hc02, hc23, hlam, hphi, p10296_1]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [hlam, p10296_0]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h10206, h6253, h7338, hc01, hc23, hlam, hphi, ht12, p10296_1]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h10116, h10206, h6253, h7338, hc01, hc23, hlam, hphi, ht12, p10296_1]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h7338, hc01, hc14, hlam, hphi, p10296_1]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h10112, hlam, p10296_0]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h10114, hlam, p10296_0]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [hlam, p10296_0]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h10116, hlam, p10296_0]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h10206, h10285, h8081, hc01, hc23, hlam, hphi, ht12, p10296_1]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h10113, hlam, p10296_1]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h10115, hlam, p10296_0]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [h10206, h10285, h8081, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10296_1]
                              · have p10296_0 := h10296c.1
                                have p10296_1 := h10296c.2.1
                                have p10296_2 := h10296c.2.2.1
                                have p10296_3 := h10296c.2.2.2
                                linarith only [hlam, p10296_0]
                        · linarith only [h0, h10206, h10291, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h10206, h10290, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h10113, h10115, h10206, h10287, h6253, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h10112, h10114, h10286, h6253, h8735, hlam]
              · linarith only [h0, h10113, h10285, hlam]
            · linarith only [h0, h10112, h10284, hlam]
      · linarith only [h10113, h10115, h8735, hlam]
    · linarith only [h10112, h10114, h8735, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h10330 | h10330
    · rcases m.htr 0 3 5 (by decide) (by decide) with h10331 | h10331
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10332 | h10332
        · linarith only [h10112, h10113, h10332, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10334 | h10334
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10335 | h10335
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10336 | h10336
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10337 | h10337
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10338 | h10338
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10339 | h10339
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10340 | h10340
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10341 | h10341
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10342 | h10342
                          · linarith only [h10112, h10113, h10332, h10334, h10341, h10342, h7338, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10344 | h10344
                            · linarith only [h10112, h10113, h10340, h10342, h10344, hlam]
                            · rcases h0bigk with h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c | h10346c
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [hlam, p10346_0]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h0, hlam, p10346_1]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h6253, hlam, p10346_0]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h7338, hlam, p10346_1]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h8081, hlam, p10346_1]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h10113, h10337, h10339, h10342, hc01, hc13, hlam, hphi, p10346_1]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [hlam, p10346_0]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h8735, hlam, p10346_0]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h10113, h10337, h10339, h10342, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p10346_1]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h10113, hlam, p10346_0]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h10334, h8735, hc01, hc12, hlam, hphi, p10346_1]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h10334, h8735, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10346_1]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [hlam, p10346_0]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h10334, h7338, h8735, hc01, hc12, hlam, hphi, p10346_1]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h10334, h8735, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10346_1]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h10337, h7338, hc01, hc13, hlam, hphi, p10346_1]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h10112, hlam, p10346_0]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h10330, hlam, p10346_0]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [hlam, p10346_0]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h10332, hlam, p10346_0]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h10337, h10339, h8081, hc01, hc13, hlam, hphi, p10346_1]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h10112, h10113, h10337, h10339, h10340, h10342, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10346_1]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h10331, hlam, p10346_0]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [h10113, h10337, h10339, h10342, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b, p10346_1]
                              · have p10346_0 := h10346c.1
                                have p10346_1 := h10346c.2.1
                                have p10346_2 := h10346c.2.2.1
                                have p10346_3 := h10346c.2.2.2
                                linarith only [hlam, p10346_0]
                        · linarith only [h10331, h10341, h8735, hlam]
                      · linarith only [h10330, h10340, h8735, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10374 | h10374
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10375 | h10375
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10376 | h10376
                          · linarith only [h0, h10112, h10339, h10376, h7338, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10378 | h10378
                            · linarith only [h10339, h10378, h7338, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h0bigk with h10380c | h10380c | h10380c | h10380c | h10380c | h10380c | h10380c | h10380c | h10380c | h10380c | h10380c | h10380c | h10380c | h10380c | h10380c | h10380c | h10380c | h10380c | h10380c | h10380c | h10380c | h10380c | h10380c | h10380c | h10380c
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [hlam, p10380_0]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h0, hlam, p10380_1]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h6253, hlam, p10380_0]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h7338, hlam, p10380_1]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h8081, hlam, p10380_1]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h10113, h10375, hc01, hc23, hlam, hphi, ht12, p10380_1]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [hlam, p10380_0]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h8735, hlam, p10380_0]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h10113, h10375, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10380_1]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h10113, hlam, p10380_0]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h10334, h6253, hc01, hc12, hlam, hphi, p10380_1]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h10112, h10334, h6253, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10380_1]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [hlam, p10380_0]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h10334, h6253, h7338, hc01, hc12, hlam, hphi, p10380_1]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h10334, h6253, h8081, hc01, hc12, hlam, hphi, p10380_1]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h7338, hc01, hc14, hlam, hphi, p10380_1]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h10112, hlam, p10380_0]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h10330, hlam, p10380_0]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [hlam, p10380_0]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h10332, hlam, p10380_0]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h8081, hc01, hc15, hlam, hphi, p10380_1]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h10113, h10375, hc02, hc23, hlam, hphi, p10380_1]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h10331, hlam, p10380_0]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [h10332, h7338, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10380_1]
                              · have p10380_0 := h10380c.1
                                have p10380_1 := h10380c.2.1
                                have p10380_2 := h10380c.2.2.1
                                have p10380_3 := h10380c.2.2.2
                                linarith only [hlam, p10380_0]
                        · linarith only [h10331, h10375, h8735, hlam]
                      · linarith only [h10330, h10374, h8735, hlam]
                  · linarith only [h10331, h10338, h6253, h8735, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h10112, h10330, h10334, h10337, h8735, hlam]
              · linarith only [h10334, h10336, h8735, hc02, hc25, hlam, hphi]
            · linarith only [h10112, h10334, h10335, h8735, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10412 | h10412
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10413 | h10413
              · linarith only [h10112, h10113, h10334, h10413, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10415 | h10415
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10416 | h10416
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10417 | h10417
                    · linarith only [h10332, h10334, h10412, h10417, h7338, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10419 | h10419
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10420 | h10420
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10421 | h10421
                          · linarith only [h0, h10112, h10413, h10417, h10420, h10421, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10423 | h10423
                            · linarith only [h0, h10413, h10421, h10423, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h0bigk with h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c | h10425c
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [hlam, p10425_0]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h0, hlam, p10425_1]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h6253, hlam, p10425_0]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h7338, hlam, p10425_1]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h8081, hlam, p10425_1]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h0, hc01, hc12, hlam, hphi, p10425_1]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [hlam, p10425_0]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h8735, hlam, p10425_0]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h0, h10413, h10421, h7338, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10425_1]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h10113, hlam, p10425_0]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h8735, hc01, hc23, hlam, hphi, ht12, p10425_1]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h8735, hc02, hc23, hlam, hphi, p10425_1]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [hlam, p10425_0]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h7338, h8735, hc01, hc23, hlam, hphi, ht12, p10425_1]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h10112, h10113, h10419, h8735, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10425_1]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h10412, h10413, h10421, h7338, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p10425_1]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h10112, hlam, p10425_0]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h10330, hlam, p10425_0]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [hlam, p10425_0]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h10332, hlam, p10425_0]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h8081, hc01, hc15, hlam, hphi, p10425_1]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h10112, h10113, h10419, h10421, hc34, hc45, hlam, hphi, p10425_1]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h10331, hlam, p10425_0]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [h10113, h10421, hc04, hc45, hlam, hphi, p10425_1]
                              · have p10425_0 := h10425c.1
                                have p10425_1 := h10425c.2.1
                                have p10425_2 := h10425c.2.2.1
                                have p10425_3 := h10425c.2.2.2
                                linarith only [hlam, p10425_0]
                        · linarith only [h10331, h10334, h10420, h6253, hlam]
                      · linarith only [h10330, h10334, h10419, h6253, hlam]
                  · linarith only [h10331, h10416, h6253, hlam]
                · linarith only [h10330, h10334, h10412, h10415, h6253, h7338, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h10112, h10412, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10456 | h10456
        · linarith only [h10112, h10331, h10456, h8735, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10458 | h10458
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10459 | h10459
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10460 | h10460
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10461 | h10461
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10462 | h10462
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10463 | h10463
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10464 | h10464
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10465 | h10465
                        · linarith only [h10112, h10331, h10458, h10465, h8735, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h10112, h10458, h10462, h10464, h10465, h8735, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h10330, h10464, h8735, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10469 | h10469
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10470 | h10470
                        · linarith only [h10331, h10458, h10470, h6253, hc01, hc12, hlam, hphi]
                        · linarith only [h10112, h10458, h10462, h10469, h10470, h8735, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h10330, h10469, h8735, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10474 | h10474
                    · linarith only [h10456, h10461, h10462, h10474, h7338, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10476 | h10476
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10477 | h10477
                        · linarith only [h10458, h10462, h10477, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10479 | h10479
                          · linarith only [h0, h10112, h10474, h10479, h8081, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10481 | h10481
                            · linarith only [h10112, h10458, h10462, h10474, h10476, h10481, h7338, h8735, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h10112, h10458, h10462, h10476, h10481, h8735, hc34, hc45, hlam, hphi]
                      · linarith only [h10112, h10330, h10476, h8735, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h10112, h10330, h10458, h10461, h8735, hlam]
              · linarith only [h10112, h10458, h10460, h8735, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h10112, h10458, h10459, h8735, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10488 | h10488
            · rcases m.htr 1 2 5 (by decide) (by decide) with h10489 | h10489
              · linarith only [h10112, h10113, h10458, h10489, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h10491 | h10491
                · rcases m.htr 1 3 5 (by decide) (by decide) with h10492 | h10492
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10493 | h10493
                    · linarith only [h10456, h10458, h10488, h10493, h7338, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10495 | h10495
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10496 | h10496
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h10497 | h10497
                          · linarith only [h0, h10112, h10489, h10493, h10496, h10497, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h10499 | h10499
                            · linarith only [h10112, h10331, h10458, h10489, h10492, h10495, h10497, h10499, h8735, hc12, hc23, hlam, hphi]
                            · rcases h0bigk with h10501c | h10501c | h10501c | h10501c | h10501c | h10501c | h10501c | h10501c | h10501c | h10501c | h10501c | h10501c | h10501c | h10501c | h10501c | h10501c | h10501c | h10501c | h10501c | h10501c | h10501c | h10501c | h10501c | h10501c | h10501c
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [hlam, p10501_0]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h0, hlam, p10501_1]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h6253, hlam, p10501_0]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h7338, hlam, p10501_1]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h8081, hlam, p10501_1]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h10331, h10458, h10492, h8735, hc01, hc23, hlam, hphi, ht12, p10501_1]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [hlam, p10501_0]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h8735, hlam, p10501_0]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h10331, h10458, h10492, h7338, h8735, hc01, hc23, hlam, hphi, ht12, p10501_1]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h10113, hlam, p10501_0]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h10331, h10458, h10492, hc01, hc23, hlam, hphi, ht12, p10501_1]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h10112, h10331, h10458, h10492, h10495, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10501_1]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [hlam, p10501_0]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h10331, h10458, h10492, h7338, hc01, hc23, hlam, hphi, ht12, p10501_1]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h10331, hlam, p10501_1]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h10488, h7338, hc01, hc12, hlam, hphi, p10501_1]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h10112, hlam, p10501_0]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h10330, hlam, p10501_0]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [hlam, p10501_0]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h10456, hlam, p10501_0]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h8081, hc01, hc15, hlam, hphi, p10501_1]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h10112, h10113, h10495, h10497, hc34, hc45, hlam, hphi, p10501_1]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h10112, h10331, h10458, h10492, h10495, h8735, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10501_1]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [h10331, h10458, h10492, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p10501_1]
                              · have p10501_0 := h10501c.1
                                have p10501_1 := h10501c.2.1
                                have p10501_2 := h10501c.2.2.1
                                have p10501_3 := h10501c.2.2.2
                                linarith only [hlam, p10501_0]
                        · linarith only [h10458, h10492, h10496, hlam]
                      · linarith only [h10330, h10458, h10495, h6253, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h10529 | h10529
                    · linarith only [h10456, h10458, h10488, h10492, h10529, h7338, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h10531 | h10531
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h10532 | h10532
                        · linarith only [h0, h10458, h10492, h10532, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h10458, h10488, h10532, h7338, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h10458, h10488, h10531, h7338, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h10330, h10491, h6253, hlam]
            · linarith only [h0, h10112, h10488, hlam]
    · linarith only [h10112, h10330, h8735, hlam]

set_option maxHeartbeats 5316000 in
set_option maxHeartbeats 5316000 in
theorem r1l7_20_11_13_14_H_I_L_I_L_I_L_I_s10_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg6253 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg7338 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg8081 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8735 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h10112 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h10539 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h6253 := hg6253
  have h7338 := hg7338
  have h8081 := hg8081
  rcases m.htr 0 3 4 (by decide) (by decide) with h10540 | h10540
  · rcases m.htr 0 3 5 (by decide) (by decide) with h10541 | h10541
    · rcases m.htr 0 4 5 (by decide) (by decide) with h10542 | h10542
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10543 | h10543
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10544 | h10544
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10545 | h10545
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10546 | h10546
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10547 | h10547
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10548 | h10548
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10549 | h10549
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10550 | h10550
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10551 | h10551
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10552 | h10552
                          · rcases h0bigk with h10553c | h10553c | h10553c | h10553c | h10553c | h10553c | h10553c | h10553c | h10553c | h10553c | h10553c | h10553c | h10553c | h10553c | h10553c | h10553c | h10553c | h10553c | h10553c | h10553c | h10553c | h10553c | h10553c | h10553c | h10553c
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [hlam, p10553_0]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h0, hlam, p10553_1]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h6253, hlam, p10553_0]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h7338, hlam, p10553_1]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h8081, hlam, p10553_1]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h10112, h10543, h10549, hc01, hc12, hlam, hphi, p10553_1]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [hlam, p10553_0]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h8735, hlam, p10553_0]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h10112, hlam, p10553_1]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h10112, h10543, h10549, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p10553_1]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h6253, hc01, hc13, hlam, hphi, p10553_1]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h10543, h8735, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p10553_1]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [hlam, p10553_0]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h10112, h10539, h10543, h10550, h8735, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10553_1]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h10543, h8081, h8735, hc01, hc12, hlam, hphi, p10553_1]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h7338, hc01, hc14, hlam, hphi, p10553_1]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h10112, h10539, h10543, h10549, h10550, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10553_1]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h10540, hlam, p10553_0]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [hlam, p10553_0]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h10112, h10543, h10549, h8081, hc01, hc12, hlam, hphi, p10553_1]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h10548, h8081, hc01, hc14, hlam, hphi, p10553_1]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h10539, hlam, p10553_1]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h10541, hlam, p10553_0]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [h10542, hlam, p10553_1]
                            · have p10553_0 := h10553c.1
                              have p10553_1 := h10553c.2.1
                              have p10553_2 := h10553c.2.2.1
                              have p10553_3 := h10553c.2.2.2
                              linarith only [hlam, p10553_0]
                          · linarith only [h10112, h10539, h10543, h10549, h10551, h10552, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h10112, h10542, h10551, hlam]
                      · linarith only [h10541, h10550, h8735, hlam]
                    · linarith only [h10540, h10549, h8735, hlam]
                  · linarith only [h10112, h10539, h10542, h10548, h7338, hc01, hc24, hlam, hphi, ht12]
                · linarith only [h10539, h10541, h10543, h10547, h6253, h8735, hc01, hc12, hlam, hphi]
              · linarith only [h10540, h10543, h10546, h8735, hlam]
            · linarith only [h10539, h10543, h10545, h8735, hlam]
          · linarith only [h10543, h10544, h8735, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10588 | h10588
          · linarith only [h10112, h10539, h10543, h10588, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10590 | h10590
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10591 | h10591
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10592 | h10592
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10593 | h10593
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10594 | h10594
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10595 | h10595
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10596 | h10596
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10597 | h10597
                          · rcases h0bigk with h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c | h10598c
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [hlam, p10598_0]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h0, hlam, p10598_1]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h6253, hlam, p10598_0]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h7338, hlam, p10598_1]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h8081, hlam, p10598_1]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h0, h10588, h10594, hc01, hc23, hlam, hphi, ht12, p10598_1]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [hlam, p10598_0]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h8735, hlam, p10598_0]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h10112, hlam, p10598_1]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h0, h10588, h10594, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10598_1]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h10543, h6253, hc01, hc23, hlam, hphi, ht12, p10598_1]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h10543, h6253, hc02, hc23, hlam, hphi, p10598_1]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [hlam, p10598_0]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h10543, h6253, h7338, hc01, hc23, hlam, hphi, ht12, p10598_1]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h10543, h6253, h8081, hc01, hc23, hlam, hphi, ht12, p10598_1]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h7338, hc01, hc14, hlam, hphi, p10598_1]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h10112, h10539, h10594, h10595, h10597, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10598_1]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h10540, hlam, p10598_0]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [hlam, p10598_0]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h10540, h10543, h6253, h8081, hc01, hc23, hlam, hphi, ht12, p10598_1]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h10588, h10590, h10594, h8081, hc01, hc23, hlam, hphi, ht12, p10598_1]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h10539, hlam, p10598_1]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h10541, hlam, p10598_0]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [h10542, hlam, p10598_1]
                            · have p10598_0 := h10598c.1
                              have p10598_1 := h10598c.2.1
                              have p10598_2 := h10598c.2.2.1
                              have p10598_3 := h10598c.2.2.2
                              linarith only [hlam, p10598_0]
                          · rcases h0bigk with h10624c | h10624c | h10624c | h10624c | h10624c | h10624c | h10624c | h10624c | h10624c | h10624c | h10624c | h10624c | h10624c | h10624c | h10624c | h10624c | h10624c | h10624c | h10624c | h10624c | h10624c | h10624c | h10624c | h10624c | h10624c
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [hlam, p10624_0]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h0, hlam, p10624_1]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h6253, hlam, p10624_0]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h7338, hlam, p10624_1]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h8081, hlam, p10624_1]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h0, h10588, h10594, hc01, hc23, hlam, hphi, ht12, p10624_1]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [hlam, p10624_0]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h8735, hlam, p10624_0]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h10112, hlam, p10624_1]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h0, h10588, h10594, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p10624_1]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h10543, h6253, hc01, hc23, hlam, hphi, ht12, p10624_1]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h10543, h6253, hc02, hc23, hlam, hphi, p10624_1]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [hlam, p10624_0]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h10543, h6253, h7338, hc01, hc23, hlam, hphi, ht12, p10624_1]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h10543, h6253, h8081, hc01, hc23, hlam, hphi, ht12, p10624_1]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h10588, h10594, h7338, hc01, hc23, hlam, hphi, ht12, p10624_1]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h10539, h10588, h10594, h7338, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p10624_1]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h10540, hlam, p10624_0]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [hlam, p10624_0]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h10588, h10594, h7338, h8081, hc01, hc23, hlam, hphi, ht12, p10624_1]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h10588, h10590, h10594, h8081, hc01, hc23, hlam, hphi, ht12, p10624_1]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h10539, hlam, p10624_1]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h10541, hlam, p10624_0]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [h10542, hlam, p10624_1]
                            · have p10624_0 := h10624c.1
                              have p10624_1 := h10624c.2.1
                              have p10624_2 := h10624c.2.2.1
                              have p10624_3 := h10624c.2.2.2
                              linarith only [hlam, p10624_0]
                        · linarith only [h0, h10588, h10596, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h10541, h10543, h10595, h6253, hlam]
                    · linarith only [h10543, h10590, h10594, h8081, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h10542, h10593, h7338, hlam]
                · linarith only [h0, h10539, h10541, h10543, h10592, h6253, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h10540, h10591, h6253, hlam]
            · linarith only [h0, h10539, h10590, hlam]
      · linarith only [h10112, h10539, h10542, hlam]
    · linarith only [h10539, h10541, h8735, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h10659 | h10659
    · rcases m.htr 0 4 5 (by decide) (by decide) with h10660 | h10660
      · rcases m.htr 1 2 3 (by decide) (by decide) with h10661 | h10661
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10662 | h10662
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10663 | h10663
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10664 | h10664
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10665 | h10665
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10666 | h10666
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10667 | h10667
                    · linarith only [h10539, h10540, h10661, h10667, h8735, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h10539, h10661, h10664, h10667, h8735, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h10660, h10666, h7338, hlam]
                · linarith only [h10659, h10665, h6253, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10672 | h10672
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10673 | h10673
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10674 | h10674
                    · linarith only [h10661, h10664, h10674, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10676 | h10676
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10677 | h10677
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10678 | h10678
                          · rcases h0bigk with h10679c | h10679c | h10679c | h10679c | h10679c | h10679c | h10679c | h10679c | h10679c | h10679c | h10679c | h10679c | h10679c | h10679c | h10679c | h10679c | h10679c | h10679c | h10679c | h10679c | h10679c | h10679c | h10679c | h10679c | h10679c
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [hlam, p10679_0]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h0, hlam, p10679_1]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h6253, hlam, p10679_0]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h7338, hlam, p10679_1]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h8081, hlam, p10679_1]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h0, hc01, hc12, hlam, hphi, p10679_1]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [hlam, p10679_0]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h8735, hlam, p10679_0]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h10112, hlam, p10679_1]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h0, h8081, hc01, hc12, hlam, hphi, p10679_1]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h10661, h10664, h8735, hc01, hc34, hlam, hphi, ht12, ht23, p10679_1]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h10661, h10664, h8735, hc02, hc34, hlam, hphi, ht23, p10679_1]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [hlam, p10679_0]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h10540, hlam, p10679_1]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h10661, h10664, h8081, h8735, hc01, hc34, hlam, hphi, ht12, ht23, p10679_1]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h10112, h10662, hc01, hc14, hlam, hphi, p10679_1]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h10112, h10539, h10662, h10676, h10678, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p10679_1]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h10540, hc03, hc34, hlam, hphi, p10679_1]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [hlam, p10679_0]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h10540, h8081, hc01, hc34, hlam, hphi, ht12, ht23, p10679_1]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h8081, hc01, hc15, hlam, hphi, p10679_1]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h10539, hlam, p10679_1]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h10659, hlam, p10679_0]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [h10660, hlam, p10679_1]
                            · have p10679_0 := h10679c.1
                              have p10679_1 := h10679c.2.1
                              have p10679_2 := h10679c.2.2.1
                              have p10679_3 := h10679c.2.2.2
                              linarith only [hlam, p10679_0]
                          · linarith only [h10664, h10678, h6253, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h10112, h10539, h10660, h10661, h10664, h10677, h7338, h8735, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h10659, h10676, h8735, hlam]
                  · linarith only [h10539, h10660, h10661, h10664, h10673, h7338, h8735, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h10539, h10659, h10661, h10672, h8735, hlam]
            · linarith only [h10539, h10663, h8735, hc12, hc23, hlam, hphi]
          · linarith only [h10661, h10662, h8735, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h10712 | h10712
          · linarith only [h10112, h10539, h10661, h10712, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h10714 | h10714
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10715 | h10715
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10716 | h10716
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10717 | h10717
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10718 | h10718
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10719 | h10719
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10720 | h10720
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10721 | h10721
                          · rcases h0bigk with h10722c | h10722c | h10722c | h10722c | h10722c | h10722c | h10722c | h10722c | h10722c | h10722c | h10722c | h10722c | h10722c | h10722c | h10722c | h10722c | h10722c | h10722c | h10722c | h10722c | h10722c | h10722c | h10722c | h10722c | h10722c
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [hlam, p10722_0]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h0, hlam, p10722_1]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h6253, hlam, p10722_0]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h7338, hlam, p10722_1]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h8081, hlam, p10722_1]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h0, h10712, h10718, hc01, hc23, hlam, hphi, ht12, p10722_1]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [hlam, p10722_0]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h8735, hlam, p10722_0]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h10112, hlam, p10722_1]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h10540, h10661, h10715, h8081, h8735, hc01, hc23, hlam, hphi, ht12, p10722_1]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h10540, h10661, h10715, hc01, hc23, hlam, hphi, ht12, p10722_1]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h10540, h10661, h10715, hc02, hc23, hlam, hphi, p10722_1]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [hlam, p10722_0]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h10540, hlam, p10722_1]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h10540, h10661, h10715, h8081, hc01, hc23, hlam, hphi, ht12, p10722_1]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h10540, h10661, h10715, hc01, hc23, hlam, hphi, ht12, p10722_1]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h10539, h10540, h10661, h10715, h10719, h10721, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p10722_1]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h10540, h10661, h10715, hc03, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p10722_1]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [hlam, p10722_0]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h10540, h10661, h10715, h8081, hc01, hc23, hlam, hphi, ht12, p10722_1]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h8081, hc01, hc15, hlam, hphi, p10722_1]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h10539, hlam, p10722_1]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h10659, hlam, p10722_0]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [h10660, hlam, p10722_1]
                            · have p10722_0 := h10722c.1
                              have p10722_1 := h10722c.2.1
                              have p10722_2 := h10722c.2.2.1
                              have p10722_3 := h10722c.2.2.2
                              linarith only [hlam, p10722_0]
                          · linarith only [h10540, h10660, h10721, hlam]
                        · linarith only [h10539, h10540, h10660, h10712, h10715, h10720, h8735, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h10540, h10661, h10715, h10719, h8735, hc02, hc35, hlam, hphi, ht23]
                    · linarith only [h10661, h10715, h10718, hlam]
                  · linarith only [h10539, h10540, h10660, h10661, h10715, h10717, h7338, h8735, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h10540, h10659, h10715, h10716, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10754 | h10754
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10755 | h10755
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10756 | h10756
                    · linarith only [h10661, h10714, h10715, h10756, h8081, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h10661, h10714, h10756, h8081, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h10539, h10660, h10661, h10755, h7338, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h10659, h10754, h6253, hlam]
            · linarith only [h0, h10539, h10714, h6253, h8735, hc01, hc13, hlam, hphi]
      · linarith only [h10539, h10540, h10660, h8735, hlam]
    · linarith only [h10539, h10659, h8735, hlam]

end R2N4
