import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 19434000 in
set_option maxHeartbeats 19434000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s20_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg15532 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg18443 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg20697 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h22350 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h30132 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h15532 := hg15532
  have h18443 := hg18443
  have h20697 := hg20697
  rcases m.htr 0 2 5 (by decide) (by decide) with h30133 | h30133
  · rcases m.htr 0 3 4 (by decide) (by decide) with h30134 | h30134
    · rcases m.htr 0 3 5 (by decide) (by decide) with h30135 | h30135
      · rcases m.htr 0 4 5 (by decide) (by decide) with h30136 | h30136
        · rcases m.htr 1 2 3 (by decide) (by decide) with h30137 | h30137
          · rcases m.htr 1 2 4 (by decide) (by decide) with h30138 | h30138
            · rcases m.htr 1 2 5 (by decide) (by decide) with h30139 | h30139
              · rcases m.htr 1 3 4 (by decide) (by decide) with h30140 | h30140
                · rcases m.htr 1 3 5 (by decide) (by decide) with h30141 | h30141
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h30142 | h30142
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h30143 | h30143
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h30144 | h30144
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h30145 | h30145
                          · linarith only [h22350, h30132, h30137, h30145, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                          · linarith only [h22350, h30132, h30136, h30137, h30145, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h22350, h30133, h30135, h30144, hc03, hc25, hlam, hphi, ht0b, ht5b]
                      · linarith only [h22350, h30134, h30143, hlam]
                    · linarith only [h0, h18443, h30132, h30136, h30142, hc01, hc12, hlam, hphi]
                  · linarith only [h15532, h22350, h30132, h30135, h30136, h30141, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h22350, h30132, h30134, h30137, h30140, hlam]
              · linarith only [h22350, h30137, h30139, hc02, hc25, hlam, hphi]
            · linarith only [h22350, h30132, h30137, h30138, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h30155 | h30155
            · rcases m.htr 1 2 5 (by decide) (by decide) with h30156 | h30156
              · rcases m.htr 1 3 4 (by decide) (by decide) with h30157 | h30157
                · rcases m.htr 1 3 5 (by decide) (by decide) with h30158 | h30158
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h30159 | h30159
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h30160 | h30160
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h30161 | h30161
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h30162 | h30162
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h30163 | h30163
                            · rcases h0bigk with h30164c | h30164c | h30164c | h30164c | h30164c | h30164c | h30164c | h30164c | h30164c | h30164c | h30164c | h30164c | h30164c | h30164c | h30164c | h30164c | h30164c | h30164c | h30164c | h30164c | h30164c | h30164c | h30164c | h30164c | h30164c
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [hlam, p30164_0]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [h0, hlam, p30164_1]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [h15532, hlam, p30164_0]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [h18443, hlam, p30164_1]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [h20697, hlam, p30164_1]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [h0, h30137, hc01, hc23, hlam, hphi, ht12, p30164_1]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [hlam, p30164_0]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [h22350, hlam, p30164_0]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [h0, h30132, h30137, h30160, h30163, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p30164_1]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [h0, h20697, h30137, hc01, hc23, hlam, hphi, ht12, p30164_1]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                rcases p30164_3 (m.d 0 1) (by simp) with h30175 | h30175
                                · linarith only [h15532, h30175, hlam]
                                · rcases p30164_3 (m.d 0 2) (by simp) with h30177 | h30177
                                  · linarith only [h22350, h30177, hlam]
                                  · linarith only [h0, h30177, hlam]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [h15532, h30132, h30137, h30160, h30163, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p30164_1]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [hlam, p30164_0]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                rcases p30164_3 (m.d 0 1) (by simp) with h30182 | h30182
                                · linarith only [h15532, h30182, hlam]
                                · rcases p30164_3 (m.d 0 2) (by simp) with h30184 | h30184
                                  · linarith only [h22350, h30184, hlam]
                                  · linarith only [h30132, h30184, hlam]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                rcases p30164_3 (m.d 0 1) (by simp) with h30187 | h30187
                                · linarith only [h15532, h30187, hlam]
                                · rcases p30164_3 (m.d 0 2) (by simp) with h30189 | h30189
                                  · linarith only [h22350, h30189, hlam]
                                  · linarith only [h30133, h30189, hlam]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [h0, h30132, h30137, hc01, hc23, hlam, hphi, ht12, p30164_1]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [h30132, hlam, p30164_0]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [h30134, hlam, p30164_0]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [hlam, p30164_0]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [h0, h20697, h30132, h30137, hc01, hc23, hlam, hphi, ht12, p30164_1]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [h0, h30133, h30137, hc01, hc23, hlam, hphi, ht12, p30164_1]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [h30133, hlam, p30164_1]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [h30135, hlam, p30164_0]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [h30136, hlam, p30164_1]
                              · have p30164_0 := h30164c.1
                                have p30164_1 := h30164c.2.1
                                have p30164_2 := h30164c.2.2.1
                                have p30164_3 := h30164c.2.2.2
                                linarith only [hlam, p30164_0]
                            · linarith only [h0, h30132, h30137, h30162, h30163, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h30203 | h30203
                            · linarith only [h30160, h30162, h30203, hlam]
                            · rcases h0bigk with h30205c | h30205c | h30205c | h30205c | h30205c | h30205c | h30205c | h30205c | h30205c | h30205c | h30205c | h30205c | h30205c | h30205c | h30205c | h30205c | h30205c | h30205c | h30205c | h30205c | h30205c | h30205c | h30205c | h30205c | h30205c
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [hlam, p30205_0]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [h0, hlam, p30205_1]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [h15532, hlam, p30205_0]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [h18443, hlam, p30205_1]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [h20697, hlam, p30205_1]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [h0, h30137, hc01, hc23, hlam, hphi, ht12, p30205_1]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [hlam, p30205_0]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [h22350, hlam, p30205_0]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [h0, h18443, h30137, hc01, hc23, hlam, hphi, ht12, p30205_1]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [h0, h20697, h30137, hc01, hc23, hlam, hphi, ht12, p30205_1]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                rcases p30205_3 (m.d 0 1) (by simp) with h30216 | h30216
                                · linarith only [h15532, h30216, hlam]
                                · rcases p30205_3 (m.d 0 2) (by simp) with h30218 | h30218
                                  · linarith only [h22350, h30218, hlam]
                                  · linarith only [h0, h30218, hlam]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [h15532, h30132, h30136, h30137, h30160, h30162, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p30205_1]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [hlam, p30205_0]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [h15532, h30136, h30137, h30160, h30162, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p30205_1]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                rcases p30205_3 (m.d 0 1) (by simp) with h30224 | h30224
                                · linarith only [h15532, h30224, hlam]
                                · rcases p30205_3 (m.d 0 2) (by simp) with h30226 | h30226
                                  · linarith only [h22350, h30226, hlam]
                                  · linarith only [h30133, h30226, hlam]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [h0, h30132, h30137, hc01, hc23, hlam, hphi, ht12, p30205_1]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [h30132, hlam, p30205_0]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [h30134, hlam, p30205_0]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [hlam, p30205_0]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [h0, h30132, h30136, h30137, h30160, h30162, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p30205_1]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [h0, h30133, h30137, hc01, hc23, hlam, hphi, ht12, p30205_1]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [h30133, hlam, p30205_1]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [h30135, hlam, p30205_0]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [h30136, hlam, p30205_1]
                              · have p30205_0 := h30205c.1
                                have p30205_1 := h30205c.2.1
                                have p30205_2 := h30205c.2.2.1
                                have p30205_3 := h30205c.2.2.2
                                linarith only [hlam, p30205_0]
                        · linarith only [h0, h30137, h30161, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h0, h30137, h30160, hc01, hc34, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h18443, h30132, h30136, h30159, hc01, hc12, hlam, hphi]
                  · linarith only [h0, h15532, h30132, h30135, h30136, h30137, h30158, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h15532, h30134, h30157, hlam]
              · linarith only [h0, h30133, h30156, hlam]
            · linarith only [h0, h30132, h30155, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h30246 | h30246
          · rcases m.htr 1 2 4 (by decide) (by decide) with h30247 | h30247
            · rcases m.htr 1 2 5 (by decide) (by decide) with h30248 | h30248
              · rcases m.htr 1 3 4 (by decide) (by decide) with h30249 | h30249
                · rcases m.htr 1 3 5 (by decide) (by decide) with h30250 | h30250
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h30251 | h30251
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h30252 | h30252
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h30253 | h30253
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h30254 | h30254
                          · linarith only [h18443, h22350, h30132, h30136, h30246, h30254, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h30256 | h30256
                            · linarith only [h18443, h22350, h30133, h30136, h30246, h30252, h30254, h30256, hc01, hc12, hlam, hphi]
                            · rcases h0bigk with h30258c | h30258c | h30258c | h30258c | h30258c | h30258c | h30258c | h30258c | h30258c | h30258c | h30258c | h30258c | h30258c | h30258c | h30258c | h30258c | h30258c | h30258c | h30258c | h30258c | h30258c | h30258c | h30258c | h30258c | h30258c
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [hlam, p30258_0]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h0, hlam, p30258_1]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h15532, hlam, p30258_0]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h18443, hlam, p30258_1]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h20697, hlam, p30258_1]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h22350, h30246, hc01, hc12, hlam, hphi, p30258_1]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [hlam, p30258_0]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h22350, hlam, p30258_0]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h18443, h22350, h30246, hc01, hc12, hlam, hphi, p30258_1]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h22350, h30246, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p30258_1]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h22350, h30246, hc01, hc12, hlam, hphi, p30258_1]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h22350, h30133, h30246, h30254, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p30258_1]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [hlam, p30258_0]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h18443, h22350, h30246, hc01, hc12, hlam, hphi, p30258_1]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h20697, h22350, h30246, hc01, hc12, hlam, hphi, p30258_1]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h30136, h30249, h30251, hc01, hc13, hlam, hphi, p30258_1]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h30132, hlam, p30258_0]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h30134, hlam, p30258_0]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [hlam, p30258_0]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h30136, hlam, p30258_0]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h22350, h30133, h30246, hc01, hc12, hlam, hphi, p30258_1]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h30133, hlam, p30258_1]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h30135, hlam, p30258_0]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [h22350, h30133, h30246, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p30258_1]
                              · have p30258_0 := h30258c.1
                                have p30258_1 := h30258c.2.1
                                have p30258_2 := h30258c.2.2.1
                                have p30258_3 := h30258c.2.2.2
                                linarith only [hlam, p30258_0]
                        · linarith only [h22350, h30135, h30253, hlam]
                      · linarith only [h22350, h30134, h30252, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h30286 | h30286
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h30287 | h30287
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h30288 | h30288
                          · linarith only [h22350, h30132, h30251, h30288, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h30290 | h30290
                            · linarith only [h18443, h30133, h30251, h30286, h30288, h30290, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · rcases h0bigk with h30292c | h30292c | h30292c | h30292c | h30292c | h30292c | h30292c | h30292c | h30292c | h30292c | h30292c | h30292c | h30292c | h30292c | h30292c | h30292c | h30292c | h30292c | h30292c | h30292c | h30292c | h30292c | h30292c | h30292c | h30292c
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [hlam, p30292_0]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h0, hlam, p30292_1]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h15532, hlam, p30292_0]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h18443, hlam, p30292_1]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h20697, hlam, p30292_1]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h22350, h30246, hc01, hc12, hlam, hphi, p30292_1]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [hlam, p30292_0]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h22350, hlam, p30292_0]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h18443, h22350, h30246, hc01, hc12, hlam, hphi, p30292_1]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h22350, h30246, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p30292_1]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h22350, h30246, hc01, hc12, hlam, hphi, p30292_1]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h22350, h30133, h30246, h30288, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p30292_1]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [hlam, p30292_0]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h18443, h22350, h30246, hc01, hc12, hlam, hphi, p30292_1]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h20697, h22350, h30246, hc01, hc12, hlam, hphi, p30292_1]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h18443, h30251, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p30292_1]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h30132, hlam, p30292_0]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h30134, hlam, p30292_0]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [hlam, p30292_0]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h30136, hlam, p30292_0]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h22350, h30133, h30246, hc01, hc12, hlam, hphi, p30292_1]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h30133, hlam, p30292_1]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h30135, hlam, p30292_0]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [h22350, h30133, h30246, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p30292_1]
                              · have p30292_0 := h30292c.1
                                have p30292_1 := h30292c.2.1
                                have p30292_2 := h30292c.2.2.1
                                have p30292_3 := h30292c.2.2.2
                                linarith only [hlam, p30292_0]
                        · linarith only [h22350, h30135, h30287, hlam]
                      · linarith only [h22350, h30134, h30286, hlam]
                  · linarith only [h15532, h22350, h30133, h30135, h30250, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h15532, h22350, h30132, h30134, h30249, hlam]
              · linarith only [h22350, h30133, h30248, hc12, hc23, hlam, hphi]
            · linarith only [h22350, h30132, h30246, h30247, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h30324 | h30324
            · rcases m.htr 1 2 5 (by decide) (by decide) with h30325 | h30325
              · rcases m.htr 1 3 4 (by decide) (by decide) with h30326 | h30326
                · rcases m.htr 1 3 5 (by decide) (by decide) with h30327 | h30327
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h30328 | h30328
                    · linarith only [h18443, h30136, h30246, h30324, h30328, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h30330 | h30330
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h30331 | h30331
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h30332 | h30332
                          · linarith only [h30132, h30136, h30332, hlam]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h30334 | h30334
                            · linarith only [h18443, h30328, h30334, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h0bigk with h30336c | h30336c | h30336c | h30336c | h30336c | h30336c | h30336c | h30336c | h30336c | h30336c | h30336c | h30336c | h30336c | h30336c | h30336c | h30336c | h30336c | h30336c | h30336c | h30336c | h30336c | h30336c | h30336c | h30336c | h30336c
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [hlam, p30336_0]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [h0, hlam, p30336_1]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [h15532, hlam, p30336_0]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [h18443, hlam, p30336_1]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [h20697, hlam, p30336_1]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [h0, h30246, hc01, hc23, hlam, hphi, ht12, p30336_1]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [hlam, p30336_0]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [h22350, hlam, p30336_0]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [h0, h18443, h30246, hc01, hc23, hlam, hphi, ht12, p30336_1]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [h0, h18443, h30136, h30246, hc01, hc23, hlam, hphi, ht12, p30336_1]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                rcases p30336_3 (m.d 0 1) (by simp) with h30347 | h30347
                                · linarith only [h15532, h30347, hlam]
                                · rcases p30336_3 (m.d 0 2) (by simp) with h30349 | h30349
                                  · linarith only [h22350, h30349, hlam]
                                  · linarith only [h0, h30349, hlam]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                rcases p30336_3 (m.d 0 1) (by simp) with h30352 | h30352
                                · linarith only [h15532, h30352, hlam]
                                · rcases p30336_3 (m.d 0 2) (by simp) with h30354 | h30354
                                  · linarith only [h22350, h30354, hlam]
                                  · rcases p30336_3 (m.d 0 3) (by simp) with h30356 | h30356
                                    · rcases p30336_3 (m.d 0 4) (by simp) with h30357 | h30357
                                      · linarith only [h30134, h30357, hlam]
                                      · rcases p30336_3 (m.d 0 5) (by simp) with h30359 | h30359
                                        · linarith only [h30135, h30359, hlam]
                                        · rcases h2bigk with h30361c | h30361c | h30361c | h30361c | h30361c | h30361c | h30361c | h30361c | h30361c | h30361c | h30361c | h30361c | h30361c | h30361c | h30361c | h30361c | h30361c | h30361c | h30361c | h30361c | h30361c | h30361c | h30361c | h30361c | h30361c
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [hlam, p30361_0]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [h0, hlam, p30361_1]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [h22350, hlam, p30361_0]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [h15532, h30246, h30330, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p30336_1, p30361_1]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [h15532, h30246, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p30336_1, p30361_1]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [h30246, hc02, hc23, hlam, hphi, p30361_1]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [hlam, p30361_0]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [h30246, hlam, p30361_0]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            rcases p30361_3 (m.d 0 2) (by simp) with h30370 | h30370
                                            · linarith only [h0, h30370, hlam]
                                            · linarith only [h30132, h30370, hlam]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            rcases p30361_3 (m.d 0 2) (by simp) with h30373 | h30373
                                            · linarith only [h0, h30373, hlam]
                                            · linarith only [h30133, h30373, hlam]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            rcases p30361_3 (m.d 0 2) (by simp) with h30376 | h30376
                                            · linarith only [h30376, hlam, p30361_0]
                                            · rcases p30361_3 (m.d 1 2) (by simp) with h30378 | h30378
                                              · linarith only [h30246, h30378, hlam]
                                              · linarith only [h0, h30378, hlam]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p30361_1]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [hlam, p30361_0]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [h15532, h30133, h30246, h30332, hlam, p30336_1, p30361_2]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [h15532, h30133, h30246, hlam, p30336_1, p30361_2]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [h30132, hlam, p30361_0]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [h30324, hlam, p30361_0]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [h30330, hlam, p30361_1]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [hlam, p30361_0]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [h30332, hlam, p30361_1]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [h30133, hlam, p30361_0]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [h30325, hlam, p30361_0]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [h30331, hlam, p30361_1]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [h15532, h30133, h30246, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p30336_1, p30361_1]
                                          · have p30361_0 := h30361c.1
                                            have p30361_1 := h30361c.2.1
                                            have p30361_2 := h30361c.2.2.1
                                            have p30361_3 := h30361c.2.2.2
                                            linarith only [hlam, p30361_0]
                                    · linarith only [h22350, h30356, hlam]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [hlam, p30336_0]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                rcases p30336_3 (m.d 0 1) (by simp) with h30397 | h30397
                                · linarith only [h15532, h30397, hlam]
                                · rcases p30336_3 (m.d 0 2) (by simp) with h30399 | h30399
                                  · linarith only [h22350, h30399, hlam]
                                  · linarith only [h30132, h30399, hlam]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                rcases p30336_3 (m.d 0 1) (by simp) with h30402 | h30402
                                · linarith only [h15532, h30402, hlam]
                                · rcases p30336_3 (m.d 0 2) (by simp) with h30404 | h30404
                                  · linarith only [h22350, h30404, hlam]
                                  · linarith only [h30133, h30404, hlam]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [h18443, h30328, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p30336_1]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [h30132, hlam, p30336_0]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [h30134, hlam, p30336_0]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [hlam, p30336_0]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [h30136, hlam, p30336_0]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [h22350, h30133, hc01, hc23, hlam, hphi, ht12, p30336_1]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [h30133, hlam, p30336_1]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [h30135, hlam, p30336_0]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [h18443, h22350, h30133, hc01, hc23, hlam, hphi, ht12, p30336_1]
                              · have p30336_0 := h30336c.1
                                have p30336_1 := h30336c.2.1
                                have p30336_2 := h30336c.2.2.1
                                have p30336_3 := h30336c.2.2.2
                                linarith only [hlam, p30336_0]
                        · linarith only [h0, h30246, h30331, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h18443, h30246, h30325, h30328, h30330, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h15532, h22350, h30133, h30135, h30327, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h15532, h22350, h30132, h30134, h30326, hlam]
              · linarith only [h0, h30133, h30325, hlam]
            · linarith only [h0, h30132, h30324, hlam]
      · linarith only [h22350, h30133, h30135, hlam]
    · linarith only [h22350, h30132, h30134, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h30425 | h30425
    · rcases m.htr 0 3 5 (by decide) (by decide) with h30426 | h30426
      · rcases m.htr 0 4 5 (by decide) (by decide) with h30427 | h30427
        · linarith only [h30132, h30133, h30427, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h30429 | h30429
          · rcases m.htr 1 2 4 (by decide) (by decide) with h30430 | h30430
            · rcases m.htr 1 2 5 (by decide) (by decide) with h30431 | h30431
              · rcases m.htr 1 3 4 (by decide) (by decide) with h30432 | h30432
                · rcases m.htr 1 3 5 (by decide) (by decide) with h30433 | h30433
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h30434 | h30434
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h30435 | h30435
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h30436 | h30436
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h30437 | h30437
                          · linarith only [h30132, h30133, h30427, h30429, h30436, h30437, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h30439 | h30439
                            · linarith only [h30132, h30133, h30435, h30437, h30439, hlam]
                            · rcases h0bigk with h30441c | h30441c | h30441c | h30441c | h30441c | h30441c | h30441c | h30441c | h30441c | h30441c | h30441c | h30441c | h30441c | h30441c | h30441c | h30441c | h30441c | h30441c | h30441c | h30441c | h30441c | h30441c | h30441c | h30441c | h30441c
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [hlam, p30441_0]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h0, hlam, p30441_1]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h15532, hlam, p30441_0]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h18443, hlam, p30441_1]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h20697, hlam, p30441_1]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h30133, h30429, h30432, h30434, h30437, hc01, hc12, hlam, hphi, p30441_1]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [hlam, p30441_0]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h22350, hlam, p30441_0]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h18443, h30133, h30429, h30432, h30434, h30437, hc01, hc12, hlam, hphi, p30441_1]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h30133, hlam, p30441_0]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h22350, h30429, hc01, hc12, hlam, hphi, p30441_1]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h22350, h30132, h30429, h30435, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p30441_1]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [hlam, p30441_0]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h18443, h22350, h30429, hc01, hc12, hlam, hphi, p30441_1]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h20697, h22350, h30429, hc01, hc12, hlam, hphi, p30441_1]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h22350, h30132, h30429, hc01, hc12, hlam, hphi, p30441_1]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h30132, hlam, p30441_0]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h30425, hlam, p30441_0]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [hlam, p30441_0]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h30427, hlam, p30441_0]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h30133, h30429, h30432, h30434, h30437, hc01, hc12, hlam, hphi, p30441_1]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h0, h30133, h30429, h30432, h30434, h30437, hc01, hc12, hlam, hphi, p30441_1]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h30426, hlam, p30441_0]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [h18443, h30133, h30429, h30432, h30434, h30437, hc01, hc12, hlam, hphi, p30441_1]
                              · have p30441_0 := h30441c.1
                                have p30441_1 := h30441c.2.1
                                have p30441_2 := h30441c.2.2.1
                                have p30441_3 := h30441c.2.2.2
                                linarith only [hlam, p30441_0]
                        · linarith only [h22350, h30426, h30436, hlam]
                      · linarith only [h22350, h30425, h30435, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h30469 | h30469
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h30470 | h30470
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h30471 | h30471
                          · linarith only [h30132, h30133, h30431, h30434, h30471, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h30473 | h30473
                            · linarith only [h15532, h20697, h30425, h30429, h30434, h30473, hc01, hc12, hlam, hphi]
                            · rcases h0bigk with h30475c | h30475c | h30475c | h30475c | h30475c | h30475c | h30475c | h30475c | h30475c | h30475c | h30475c | h30475c | h30475c | h30475c | h30475c | h30475c | h30475c | h30475c | h30475c | h30475c | h30475c | h30475c | h30475c | h30475c | h30475c
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [hlam, p30475_0]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h0, hlam, p30475_1]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h15532, hlam, p30475_0]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h18443, hlam, p30475_1]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h20697, hlam, p30475_1]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h30133, h30431, hc01, hc15, hlam, hphi, p30475_1]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [hlam, p30475_0]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h22350, hlam, p30475_0]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h18443, h30133, h30431, hc01, hc15, hlam, hphi, p30475_1]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h30133, hlam, p30475_0]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h22350, h30429, hc01, hc12, hlam, hphi, p30475_1]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h22350, h30132, h30429, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p30475_1]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [hlam, p30475_0]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h18443, h22350, h30429, hc01, hc12, hlam, hphi, p30475_1]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h20697, h22350, h30429, hc01, hc12, hlam, hphi, p30475_1]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h18443, h30434, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p30475_1]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h30132, hlam, p30475_0]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h30425, hlam, p30475_0]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [hlam, p30475_0]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h30427, hlam, p30475_0]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h22350, h30426, h30429, hc01, hc12, hlam, hphi, p30475_1]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h22350, h30132, h30426, h30429, h30469, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p30475_1]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h30426, hlam, p30475_0]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [h18443, h22350, h30426, h30429, hc01, hc12, hlam, hphi, p30475_1]
                              · have p30475_0 := h30475c.1
                                have p30475_1 := h30475c.2.1
                                have p30475_2 := h30475c.2.2.1
                                have p30475_3 := h30475c.2.2.2
                                linarith only [hlam, p30475_0]
                        · linarith only [h22350, h30426, h30470, hlam]
                      · linarith only [h22350, h30425, h30469, hlam]
                  · linarith only [h15532, h22350, h30426, h30433, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h22350, h30132, h30425, h30429, h30432, hlam]
              · linarith only [h22350, h30429, h30431, hc02, hc25, hlam, hphi]
            · linarith only [h22350, h30132, h30429, h30430, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h30507 | h30507
            · rcases m.htr 1 2 5 (by decide) (by decide) with h30508 | h30508
              · linarith only [h30132, h30133, h30429, h30508, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h30510 | h30510
                · rcases m.htr 1 3 5 (by decide) (by decide) with h30511 | h30511
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h30512 | h30512
                    · linarith only [h18443, h30427, h30429, h30507, h30512, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h30514 | h30514
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h30515 | h30515
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h30516 | h30516
                          · linarith only [h0, h30132, h30508, h30512, h30515, h30516, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h30518 | h30518
                            · linarith only [h0, h30508, h30516, h30518, hc01, hc34, hlam, hphi, ht12, ht23]
                            · rcases h0bigk with h30520c | h30520c | h30520c | h30520c | h30520c | h30520c | h30520c | h30520c | h30520c | h30520c | h30520c | h30520c | h30520c | h30520c | h30520c | h30520c | h30520c | h30520c | h30520c | h30520c | h30520c | h30520c | h30520c | h30520c | h30520c
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                linarith only [hlam, p30520_0]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                linarith only [h0, hlam, p30520_1]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                linarith only [h15532, hlam, p30520_0]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                linarith only [h18443, hlam, p30520_1]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                linarith only [h20697, hlam, p30520_1]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                linarith only [h0, h30508, h30515, hc01, hc23, hlam, hphi, ht12, p30520_1]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                linarith only [hlam, p30520_0]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                linarith only [h22350, hlam, p30520_0]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                linarith only [h0, h30508, h30516, hc04, hc45, hlam, hphi, p30520_1]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                linarith only [h30133, hlam, p30520_0]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                rcases p30520_3 (m.d 0 1) (by simp) with h30531 | h30531
                                · linarith only [h15532, h30531, hlam]
                                · rcases p30520_3 (m.d 0 2) (by simp) with h30533 | h30533
                                  · linarith only [h22350, h30533, hlam]
                                  · linarith only [h0, h30533, hlam]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                rcases p30520_3 (m.d 0 1) (by simp) with h30536 | h30536
                                · linarith only [h15532, h30536, hlam]
                                · rcases p30520_3 (m.d 0 2) (by simp) with h30538 | h30538
                                  · linarith only [h22350, h30538, hlam]
                                  · rcases p30520_3 (m.d 0 3) (by simp) with h30540 | h30540
                                    · rcases p30520_3 (m.d 0 4) (by simp) with h30541 | h30541
                                      · linarith only [h30425, h30541, hlam]
                                      · rcases p30520_3 (m.d 0 5) (by simp) with h30543 | h30543
                                        · linarith only [h30426, h30543, hlam]
                                        · linarith only [h30133, h30543, hlam]
                                    · linarith only [h22350, h30540, hlam]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                linarith only [hlam, p30520_0]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                rcases p30520_3 (m.d 0 1) (by simp) with h30548 | h30548
                                · linarith only [h15532, h30548, hlam]
                                · rcases p30520_3 (m.d 0 2) (by simp) with h30550 | h30550
                                  · linarith only [h22350, h30550, hlam]
                                  · linarith only [h30132, h30550, hlam]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                rcases p30520_3 (m.d 0 1) (by simp) with h30553 | h30553
                                · linarith only [h15532, h30553, hlam]
                                · rcases p30520_3 (m.d 0 2) (by simp) with h30555 | h30555
                                  · linarith only [h22350, h30555, hlam]
                                  · rcases p30520_3 (m.d 0 3) (by simp) with h30557 | h30557
                                    · rcases p30520_3 (m.d 0 4) (by simp) with h30558 | h30558
                                      · linarith only [h30425, h30558, hlam]
                                      · rcases p30520_3 (m.d 0 5) (by simp) with h30560 | h30560
                                        · linarith only [h30426, h30560, hlam]
                                        · rcases h2bigk with h30562c | h30562c | h30562c | h30562c | h30562c | h30562c | h30562c | h30562c | h30562c | h30562c | h30562c | h30562c | h30562c | h30562c | h30562c | h30562c | h30562c | h30562c | h30562c | h30562c | h30562c | h30562c | h30562c | h30562c | h30562c
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [hlam, p30562_0]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [h0, hlam, p30562_1]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [h22350, hlam, p30562_0]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [h15532, h30133, h30429, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p30520_1, p30562_1]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [h30133, hlam, p30562_0]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [h30508, hc02, hc25, hlam, hphi, p30562_1]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [hlam, p30562_0]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [h30429, hlam, p30562_0]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [h30508, h30514, h30516, hc34, hc45, hlam, hphi, p30562_1]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [h30508, hlam, p30562_0]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            rcases p30562_3 (m.d 0 2) (by simp) with h30573 | h30573
                                            · linarith only [h30573, hlam, p30562_0]
                                            · rcases p30562_3 (m.d 1 2) (by simp) with h30575 | h30575
                                              · linarith only [h30429, h30575, hlam]
                                              · linarith only [h0, h30575, hlam]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [h0, hc01, hc23, hlam, hphi, ht12, p30562_1]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [hlam, p30562_0]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [h15532, h30132, h30133, h30429, hlam, p30520_1, p30562_2]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [h30132, h30133, h30514, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p30562_1]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [h30132, hlam, p30562_0]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [h30507, hlam, p30562_0]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [h30514, hlam, p30562_1]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [hlam, p30562_0]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [h30516, hlam, p30562_1]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [h30132, h30514, h30516, hc34, hc45, hlam, hphi, p30562_1]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [h18443, h30507, hc01, hc25, hlam, hphi, ht12, p30562_1]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [h30515, hlam, p30562_1]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            rcases p30562_3 (m.d 0 2) (by simp) with h30590 | h30590
                                            · linarith only [h30133, h30590, hlam]
                                            · linarith only [h30132, h30590, hlam]
                                          · have p30562_0 := h30562c.1
                                            have p30562_1 := h30562c.2.1
                                            have p30562_2 := h30562c.2.2.1
                                            have p30562_3 := h30562c.2.2.2
                                            linarith only [hlam, p30562_0]
                                    · linarith only [h30426, h30557, hlam]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                linarith only [h22350, h30132, hc01, hc23, hlam, hphi, ht12, p30520_1]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                linarith only [h30132, hlam, p30520_0]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                linarith only [h30425, hlam, p30520_0]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                linarith only [hlam, p30520_0]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                linarith only [h30427, hlam, p30520_0]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                rcases p30520_3 (m.d 0 1) (by simp) with h30600 | h30600
                                · linarith only [h20697, h30600, hlam]
                                · rcases p30520_3 (m.d 0 2) (by simp) with h30602 | h30602
                                  · linarith only [h30133, h30602, hlam]
                                  · linarith only [h0, h30602, hlam]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                linarith only [h30132, h30133, h30514, h30516, hc34, hc45, hlam, hphi, p30520_1]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                linarith only [h30426, hlam, p30520_0]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                rcases p30520_3 (m.d 0 1) (by simp) with h30607 | h30607
                                · linarith only [h20697, h30607, hlam]
                                · rcases p30520_3 (m.d 0 2) (by simp) with h30609 | h30609
                                  · linarith only [h30133, h30609, hlam]
                                  · linarith only [h30132, h30609, hlam]
                              · have p30520_0 := h30520c.1
                                have p30520_1 := h30520c.2.1
                                have p30520_2 := h30520c.2.2.1
                                have p30520_3 := h30520c.2.2.2
                                linarith only [hlam, p30520_0]
                        · linarith only [h15532, h30426, h30429, h30515, hlam]
                      · linarith only [h15532, h30425, h30429, h30514, hlam]
                  · linarith only [h15532, h30426, h30511, hlam]
                · linarith only [h15532, h18443, h30425, h30429, h30507, h30510, hc01, hc23, hlam, hphi, ht12]
            · linarith only [h0, h30132, h30507, hlam]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h30618 | h30618
        · linarith only [h22350, h30132, h30426, h30618, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h30620 | h30620
          · rcases m.htr 1 2 4 (by decide) (by decide) with h30621 | h30621
            · rcases m.htr 1 2 5 (by decide) (by decide) with h30622 | h30622
              · rcases m.htr 1 3 4 (by decide) (by decide) with h30623 | h30623
                · rcases m.htr 1 3 5 (by decide) (by decide) with h30624 | h30624
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h30625 | h30625
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h30626 | h30626
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h30627 | h30627
                        · linarith only [h22350, h30132, h30426, h30620, h30627, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h22350, h30132, h30620, h30624, h30626, h30627, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h22350, h30425, h30626, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h30631 | h30631
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h30632 | h30632
                        · linarith only [h15532, h30426, h30620, h30632, hc01, hc12, hlam, hphi]
                        · linarith only [h22350, h30132, h30620, h30624, h30631, h30632, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h22350, h30425, h30631, hlam]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h30636 | h30636
                    · linarith only [h18443, h30618, h30623, h30624, h30636, hc01, hc35, hlam, hphi, ht12, ht23]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h30638 | h30638
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h30639 | h30639
                        · linarith only [h30620, h30624, h30639, hlam]
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h30641 | h30641
                          · linarith only [h0, h20697, h30132, h30636, h30641, hc01, hc12, hlam, hphi]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h30643 | h30643
                            · linarith only [h18443, h22350, h30132, h30620, h30624, h30636, h30638, h30643, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h22350, h30132, h30620, h30624, h30638, h30643, hc34, hc45, hlam, hphi]
                      · linarith only [h22350, h30132, h30425, h30638, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h22350, h30132, h30425, h30620, h30623, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
              · linarith only [h22350, h30132, h30620, h30622, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
            · linarith only [h22350, h30132, h30620, h30621, hlam]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h30650 | h30650
            · rcases m.htr 1 2 5 (by decide) (by decide) with h30651 | h30651
              · linarith only [h30132, h30133, h30620, h30651, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h30653 | h30653
                · rcases m.htr 1 3 5 (by decide) (by decide) with h30654 | h30654
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h30655 | h30655
                    · linarith only [h18443, h30618, h30620, h30650, h30655, hc01, hc23, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h30657 | h30657
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h30658 | h30658
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h30659 | h30659
                          · linarith only [h0, h20697, h30132, h30651, h30655, h30658, h30659, hc01, hc23, hlam, hphi, ht12]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h30661 | h30661
                            · linarith only [h18443, h30132, h30650, h30651, h30657, h30659, h30661, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                            · rcases h0bigk with h30663c | h30663c | h30663c | h30663c | h30663c | h30663c | h30663c | h30663c | h30663c | h30663c | h30663c | h30663c | h30663c | h30663c | h30663c | h30663c | h30663c | h30663c | h30663c | h30663c | h30663c | h30663c | h30663c | h30663c | h30663c
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [hlam, p30663_0]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h0, hlam, p30663_1]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h15532, hlam, p30663_0]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h18443, hlam, p30663_1]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h20697, hlam, p30663_1]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h22350, h30426, h30620, h30654, hc01, hc23, hlam, hphi, ht12, p30663_1]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [hlam, p30663_0]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h22350, hlam, p30663_0]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h22350, h30426, h30620, h30654, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p30663_1]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h30133, hlam, p30663_0]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h30426, h30620, h30654, hc01, hc23, hlam, hphi, ht12, p30663_1]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h30426, h30620, h30654, hc02, hc23, hlam, hphi, p30663_1]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [hlam, p30663_0]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h18443, h30426, h30620, h30654, hc01, hc23, hlam, hphi, ht12, p30663_1]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h30426, hlam, p30663_1]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h0, h30132, h30651, h30659, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p30663_1]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h30132, hlam, p30663_0]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h30425, hlam, p30663_0]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [hlam, p30663_0]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h30618, hlam, p30663_0]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h30426, h30620, h30654, hc01, hc23, hlam, hphi, ht12, p30663_1]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h30132, h30426, h30620, h30654, h30657, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p30663_1]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h15532, h30426, h30620, h30654, hc01, hc23, hlam, hphi, ht12, p30663_1]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [h18443, h30426, h30620, h30654, hc01, hc23, hlam, hphi, ht12, p30663_1]
                              · have p30663_0 := h30663c.1
                                have p30663_1 := h30663c.2.1
                                have p30663_2 := h30663c.2.2.1
                                have p30663_3 := h30663c.2.2.2
                                linarith only [hlam, p30663_0]
                        · linarith only [h30620, h30654, h30658, hlam]
                      · linarith only [h15532, h22350, h30132, h30425, h30657, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h30691 | h30691
                    · linarith only [h18443, h30618, h30650, h30651, h30691, hc01, hc25, hlam, hphi, ht12]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h30693 | h30693
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h30694 | h30694
                        · linarith only [h0, h30620, h30654, h30694, hc01, hc23, hlam, hphi, ht12]
                        · linarith only [h18443, h30620, h30650, h30694, hc01, hc35, hlam, hphi, ht12, ht23]
                      · linarith only [h18443, h30620, h30650, h30693, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h15532, h22350, h30132, h30425, h30653, hlam]
            · linarith only [h0, h15532, h22350, h30132, h30650, hc01, hc13, hlam, hphi]
    · linarith only [h22350, h30132, h30425, hlam]

end R2N4
