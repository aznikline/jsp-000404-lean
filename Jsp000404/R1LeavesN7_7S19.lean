import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_7S18

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h12237 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h12238 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  rcases m.htr 1 2 3 (by decide) (by decide) with h13115 | h13115
  · rcases m.htr 1 2 4 (by decide) (by decide) with h13116 | h13116
    · rcases m.htr 1 2 5 (by decide) (by decide) with h13117 | h13117
      · rcases m.htr 1 3 4 (by decide) (by decide) with h13118 | h13118
        · rcases m.htr 1 3 5 (by decide) (by decide) with h13119 | h13119
          · rcases m.htr 1 4 5 (by decide) (by decide) with h13120 | h13120
            · rcases m.htr 2 3 4 (by decide) (by decide) with h13121 | h13121
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13122 | h13122
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13123 | h13123
                  · linarith only [h12234, h12238, h13123, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13125 | h13125
                    · linarith only [h12233, h12238, h13121, h13125, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h1bigk with h13127c | h13127c | h13127c | h13127c | h13127c | h13127c | h13127c | h13127c | h13127c | h13127c | h13127c | h13127c | h13127c | h13127c | h13127c | h13127c | h13127c | h13127c | h13127c | h13127c | h13127c | h13127c | h13127c | h13127c | h13127c
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [hlam, p13127_0]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [h0, hlam, p13127_0]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [h10472, hlam, p13127_0]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [h11379, hlam, p13127_0]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [h12013, hlam, p13127_0]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        rcases p13127_3 (m.d 0 1) (by simp) with h13133 | h13133
                        · linarith only [h13133, hlam, p13127_0]
                        · rcases p13127_3 (m.d 1 2) (by simp) with h13135 | h13135
                          · rcases p13127_3 (m.d 1 3) (by simp) with h13136 | h13136
                            · linarith only [h13115, h13136, hlam]
                            · linarith only [h10472, h13136, hlam]
                          · linarith only [h13135, hlam, p13127_0]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [hlam, p13127_0]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [h11379, h12238, h13118, h13120, hc01, hc12, hlam, hphi, p13127_1]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [h11379, h12238, h13120, hc01, hc12, hlam, hphi, p13127_1]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [h12013, hc01, hc12, hlam, hphi, p13127_1]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        rcases p13127_3 (m.d 0 1) (by simp) with h13144 | h13144
                        · linarith only [h13144, hlam, p13127_0]
                        · rcases p13127_3 (m.d 1 2) (by simp) with h13146 | h13146
                          · rcases p13127_3 (m.d 1 3) (by simp) with h13147 | h13147
                            · rcases p13127_3 (m.d 1 4) (by simp) with h13148 | h13148
                              · linarith only [h13118, h13148, hlam]
                              · linarith only [h11379, h13148, hlam]
                            · linarith only [h13147, hlam, p13127_0]
                          · linarith only [h0, h13146, hlam]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [h13115, hlam, p13127_1]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [hlam, p13127_0]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [h11379, h12238, h13120, hc01, hc13, hlam, hphi, p13127_1]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [h11379, h12238, h13115, h13120, hc01, hc12, hlam, hphi, p13127_1]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        rcases p13127_3 (m.d 0 1) (by simp) with h13157 | h13157
                        · linarith only [h13157, hlam, p13127_0]
                        · rcases p13127_3 (m.d 1 2) (by simp) with h13159 | h13159
                          · rcases p13127_3 (m.d 1 3) (by simp) with h13160 | h13160
                            · rcases p13127_3 (m.d 1 4) (by simp) with h13161 | h13161
                              · rcases p13127_3 (m.d 1 5) (by simp) with h13162 | h13162
                                · linarith only [h13120, h13162, hlam]
                                · linarith only [h12013, h13162, hlam]
                              · linarith only [h13161, hlam, p13127_0]
                            · linarith only [h10472, h13160, hlam]
                          · linarith only [h0, h13159, hlam]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [h13116, hlam, p13127_1]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [h13118, hlam, p13127_0]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [hlam, p13127_0]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [h11379, h12238, h13120, hc01, hc14, hlam, hphi, p13127_1]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        rcases p13127_3 (m.d 0 1) (by simp) with h13172 | h13172
                        · linarith only [h13172, hlam, p13127_0]
                        · rcases p13127_3 (m.d 1 2) (by simp) with h13174 | h13174
                          · rcases p13127_3 (m.d 1 3) (by simp) with h13175 | h13175
                            · rcases p13127_3 (m.d 1 4) (by simp) with h13176 | h13176
                              · rcases p13127_3 (m.d 1 5) (by simp) with h13177 | h13177
                                · rcases h1emax with h13178 | h13178 | h13178 | h13178 | h13178
                                  · rcases h3bigk with h13179c | h13179c | h13179c | h13179c | h13179c | h13179c | h13179c | h13179c | h13179c | h13179c | h13179c | h13179c | h13179c | h13179c | h13179c | h13179c | h13179c | h13179c | h13179c | h13179c | h13179c | h13179c | h13179c | h13179c | h13179c
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [hlam, p13179_0]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [h10472, hlam, p13179_1]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [h10472, h13115, h13122, hc12, hlam, hphi, ht01, ht0b, ht5b, p13179_1, u5ehi3]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      rcases p13179_3 (m.d 0 3) (by simp) with h13183 | h13183
                                      · rcases p13179_3 (m.d 1 3) (by simp) with h13184 | h13184
                                        · rcases p13179_3 (m.d 2 3) (by simp) with h13185 | h13185
                                          · linarith only [h12233, h13185, hlam]
                                          · linarith only [h13121, h13185, hlam]
                                        · linarith only [h13118, h13184, hlam]
                                      · linarith only [h13183, hlam, p13179_0]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      rcases p13179_3 (m.d 0 3) (by simp) with h13190 | h13190
                                      · rcases p13179_3 (m.d 1 3) (by simp) with h13191 | h13191
                                        · rcases p13179_3 (m.d 2 3) (by simp) with h13192 | h13192
                                          · linarith only [h12233, h13192, hlam]
                                          · linarith only [h13122, h13192, hlam]
                                        · linarith only [h13119, h13191, hlam]
                                      · linarith only [h13190, hlam, p13179_0]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [h12233, h13115, h13122, hc12, hlam, hphi, ht01, ht0b, ht5b, p13179_1, u5ehi3]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [hlam, p13179_0]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [h13115, h13122, hc12, hlam, hphi, ht01, ht0b, ht5b, p13179_1, u5ehi3]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      rcases p13179_3 (m.d 0 3) (by simp) with h13200 | h13200
                                      · linarith only [h10472, h13200, hlam]
                                      · linarith only [h12236, h13200, hlam]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      rcases p13179_3 (m.d 0 3) (by simp) with h13203 | h13203
                                      · linarith only [h10472, h13203, hlam]
                                      · linarith only [h12237, h13203, hlam]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [h12233, hlam, p13179_0]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [h13115, hlam, p13179_0]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [hlam, p13179_0]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      rcases p13179_3 (m.d 0 3) (by simp) with h13209 | h13209
                                      · rcases p13179_3 (m.d 1 3) (by simp) with h13210 | h13210
                                        · rcases p13179_3 (m.d 2 3) (by simp) with h13211 | h13211
                                          · rcases p13179_3 (m.d 3 4) (by simp) with h13212 | h13212
                                            · linarith only [h13212, hlam, p13179_0]
                                            · rcases p13179_3 (m.d 3 5) (by simp) with h13214 | h13214
                                              · linarith only [h13122, h13214, hlam]
                                              · linarith only [h13125, h13214, hlam]
                                          · linarith only [h13211, hlam, p13179_0]
                                        · linarith only [h13118, h13210, hlam]
                                      · linarith only [h12236, h13209, hlam]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [h0, h12233, hc12, hlam, hphi, ht01, ht0b, ht5b, p13179_1, u5ehi3]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [h12236, hlam, p13179_0]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [h13118, hlam, p13179_0]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [h13121, hlam, p13179_0]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [hlam, p13179_0]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [h13125, hlam, p13179_1]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [h12237, hlam, p13179_0]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [h13119, hlam, p13179_0]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [h13122, hlam, p13179_0]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [h0, h12233, h13122, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13179_1]
                                    · have p13179_0 := h13179c.1
                                      have p13179_1 := h13179c.2.1
                                      have p13179_2 := h13179c.2.2.1
                                      have p13179_3 := h13179c.2.2.2
                                      linarith only [hlam, p13179_0]
                                  · linarith only [h0, h12233, h13122, h13178, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                  · linarith only [h10472, h13178, hc01, hlam]
                                  · linarith only [h11379, h12238, h13120, h13178, hc01, hlam]
                                  · linarith only [h13178, hc01, hlam, p13127_1]
                                · linarith only [h13177, hlam, p13127_0]
                              · linarith only [h11379, h13176, hlam]
                            · linarith only [h10472, h13175, hlam]
                          · linarith only [h0, h13174, hlam]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [h13117, hlam, p13127_1]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [h13119, hlam, p13127_0]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [h13120, hlam, p13127_0]
                      · have p13127_0 := h13127c.1
                        have p13127_1 := h13127c.2.1
                        have p13127_2 := h13127c.2.2.1
                        have p13127_3 := h13127c.2.2.2
                        linarith only [hlam, p13127_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13243 | h13243
                  · linarith only [h12234, h12238, h13243, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13245 | h13245
                    · linarith only [h12237, h12238, h13121, h13122, h13245, hc04, hc05, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h1bigk with h13247c | h13247c | h13247c | h13247c | h13247c | h13247c | h13247c | h13247c | h13247c | h13247c | h13247c | h13247c | h13247c | h13247c | h13247c | h13247c | h13247c | h13247c | h13247c | h13247c | h13247c | h13247c | h13247c | h13247c | h13247c
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [hlam, p13247_0]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [h0, hlam, p13247_0]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [h10472, hlam, p13247_0]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [h11379, hlam, p13247_0]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [h12013, hlam, p13247_0]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        rcases p13247_3 (m.d 0 1) (by simp) with h13253 | h13253
                        · linarith only [h13253, hlam, p13247_0]
                        · rcases p13247_3 (m.d 1 2) (by simp) with h13255 | h13255
                          · rcases p13247_3 (m.d 1 3) (by simp) with h13256 | h13256
                            · linarith only [h13115, h13256, hlam]
                            · linarith only [h10472, h13256, hlam]
                          · linarith only [h13255, hlam, p13247_0]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [hlam, p13247_0]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [h12238, h13118, h13120, hc12, hlam, hphi, ht01, ht0b, ht5b, p13247_1, u5ehi0]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [h12237, h12238, h13120, h13121, h13122, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13247_1]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [h12013, hc01, hc12, hlam, hphi, p13247_1]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        rcases p13247_3 (m.d 0 1) (by simp) with h13264 | h13264
                        · linarith only [h13264, hlam, p13247_0]
                        · rcases p13247_3 (m.d 1 2) (by simp) with h13266 | h13266
                          · rcases p13247_3 (m.d 1 3) (by simp) with h13267 | h13267
                            · rcases p13247_3 (m.d 1 4) (by simp) with h13268 | h13268
                              · linarith only [h13118, h13268, hlam]
                              · linarith only [h11379, h13268, hlam]
                            · linarith only [h13267, hlam, p13247_0]
                          · linarith only [h0, h13266, hlam]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [h13115, hlam, p13247_1]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [hlam, p13247_0]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [h12237, h12238, h13120, h13121, h13122, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13247_1]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [h12237, h12238, h13115, h13120, h13121, h13122, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13247_1]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        rcases p13247_3 (m.d 0 1) (by simp) with h13277 | h13277
                        · linarith only [h13277, hlam, p13247_0]
                        · rcases p13247_3 (m.d 1 2) (by simp) with h13279 | h13279
                          · rcases p13247_3 (m.d 1 3) (by simp) with h13280 | h13280
                            · rcases p13247_3 (m.d 1 4) (by simp) with h13281 | h13281
                              · rcases p13247_3 (m.d 1 5) (by simp) with h13282 | h13282
                                · linarith only [h13120, h13282, hlam]
                                · linarith only [h12013, h13282, hlam]
                              · linarith only [h13281, hlam, p13247_0]
                            · linarith only [h10472, h13280, hlam]
                          · linarith only [h0, h13279, hlam]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [h13116, hlam, p13247_1]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [h13118, hlam, p13247_0]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [hlam, p13247_0]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [h12237, h12238, h13120, h13121, h13122, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13247_1]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        rcases p13247_3 (m.d 0 1) (by simp) with h13292 | h13292
                        · linarith only [h13292, hlam, p13247_0]
                        · rcases p13247_3 (m.d 1 2) (by simp) with h13294 | h13294
                          · rcases p13247_3 (m.d 1 3) (by simp) with h13295 | h13295
                            · rcases p13247_3 (m.d 1 4) (by simp) with h13296 | h13296
                              · rcases p13247_3 (m.d 1 5) (by simp) with h13297 | h13297
                                · rcases h1emax with h13298 | h13298 | h13298 | h13298 | h13298
                                  · rcases h3bigk with h13299c | h13299c | h13299c | h13299c | h13299c | h13299c | h13299c | h13299c | h13299c | h13299c | h13299c | h13299c | h13299c | h13299c | h13299c | h13299c | h13299c | h13299c | h13299c | h13299c | h13299c | h13299c | h13299c | h13299c | h13299c
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [hlam, p13299_0]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [h10472, hlam, p13299_1]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      rcases p13299_3 (m.d 0 3) (by simp) with h13302 | h13302
                                      · rcases p13299_3 (m.d 1 3) (by simp) with h13303 | h13303
                                        · rcases p13299_3 (m.d 2 3) (by simp) with h13304 | h13304
                                          · linarith only [h12233, h13304, hlam]
                                          · rcases p13299_3 (m.d 3 4) (by simp) with h13306 | h13306
                                            · linarith only [h12236, h13306, hlam]
                                            · rcases p13299_3 (m.d 3 5) (by simp) with h13308 | h13308
                                              · linarith only [h12237, h13308, hlam]
                                              · linarith only [h13122, h13308, hlam]
                                        · linarith only [h13115, h13303, hlam]
                                      · linarith only [h12233, h13302, hlam]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [h12237, h13121, h13122, hlam, p13299_2]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [h13121, h13122, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p13299_1]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [h12237, h13115, h13121, h13122, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13299_1]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [hlam, p13299_0]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      rcases p13299_3 (m.d 0 3) (by simp) with h13317 | h13317
                                      · linarith only [h10472, h13317, hlam]
                                      · linarith only [h12233, h13317, hlam]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [h10472, h12237, h13121, h13122, hlam, p13299_2]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [h13121, h13122, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13299_1]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [h12233, hlam, p13299_0]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [h13115, hlam, p13299_0]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [hlam, p13299_0]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [h12237, h13122, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p13299_1]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [h13122, hlam, p13299_0]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [h12236, hlam, p13299_0]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [h13118, hlam, p13299_0]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [h13121, hlam, p13299_0]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [hlam, p13299_0]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [h13245, hlam, p13299_1]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [h12237, hlam, p13299_0]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [h13119, hlam, p13299_0]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [h12237, h12238, h13115, h13118, h13120, h13121, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13299_1]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      rcases p13299_3 (m.d 0 3) (by simp) with h13335 | h13335
                                      · rcases p13299_3 (m.d 1 3) (by simp) with h13336 | h13336
                                        · rcases p13299_3 (m.d 2 3) (by simp) with h13337 | h13337
                                          · linarith only [h13122, h13337, hlam]
                                          · linarith only [h13121, h13337, hlam]
                                        · linarith only [h13118, h13336, hlam]
                                      · linarith only [h12236, h13335, hlam]
                                    · have p13299_0 := h13299c.1
                                      have p13299_1 := h13299c.2.1
                                      have p13299_2 := h13299c.2.2.1
                                      have p13299_3 := h13299c.2.2.2
                                      linarith only [hlam, p13299_0]
                                  · linarith only [h12238, h13115, h13118, h13120, h13298, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                                  · linarith only [h12237, h12238, h13118, h13120, h13121, h13122, h13298, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h12237, h12238, h13120, h13121, h13122, h13298, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h13298, hc01, hlam, p13247_1]
                                · linarith only [h13297, hlam, p13247_0]
                              · linarith only [h11379, h13296, hlam]
                            · linarith only [h10472, h13295, hlam]
                          · linarith only [h0, h13294, hlam]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [h13117, hlam, p13247_1]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [h13119, hlam, p13247_0]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [h13120, hlam, p13247_0]
                      · have p13247_0 := h13247c.1
                        have p13247_1 := h13247c.2.1
                        have p13247_2 := h13247c.2.2.1
                        have p13247_3 := h13247c.2.2.2
                        linarith only [hlam, p13247_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13355 | h13355
                · linarith only [h12236, h12238, h13115, h13118, h13120, h13121, h13355, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13357 | h13357
                  · linarith only [h0, h12234, h12236, h12238, h13121, h13357, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13359 | h13359
                    · linarith only [h12236, h12238, h13359, hlam]
                    · rcases h1bigk with h13361c | h13361c | h13361c | h13361c | h13361c | h13361c | h13361c | h13361c | h13361c | h13361c | h13361c | h13361c | h13361c | h13361c | h13361c | h13361c | h13361c | h13361c | h13361c | h13361c | h13361c | h13361c | h13361c | h13361c | h13361c
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [hlam, p13361_0]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [h0, hlam, p13361_0]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [h10472, hlam, p13361_0]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [h11379, hlam, p13361_0]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [h12013, hlam, p13361_0]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        rcases p13361_3 (m.d 0 1) (by simp) with h13367 | h13367
                        · linarith only [h13367, hlam, p13361_0]
                        · rcases p13361_3 (m.d 1 2) (by simp) with h13369 | h13369
                          · rcases p13361_3 (m.d 1 3) (by simp) with h13370 | h13370
                            · linarith only [h13115, h13370, hlam]
                            · linarith only [h10472, h13370, hlam]
                          · linarith only [h13369, hlam, p13361_0]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [hlam, p13361_0]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [h12236, h12238, h13118, h13120, h13121, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13361_1]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [h12236, h12238, h13120, h13121, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13361_1]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [h12013, hc01, hc12, hlam, hphi, p13361_1]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        rcases p13361_3 (m.d 0 1) (by simp) with h13378 | h13378
                        · linarith only [h13378, hlam, p13361_0]
                        · rcases p13361_3 (m.d 1 2) (by simp) with h13380 | h13380
                          · rcases p13361_3 (m.d 1 3) (by simp) with h13381 | h13381
                            · rcases p13361_3 (m.d 1 4) (by simp) with h13382 | h13382
                              · linarith only [h13118, h13382, hlam]
                              · linarith only [h11379, h13382, hlam]
                            · linarith only [h13381, hlam, p13361_0]
                          · linarith only [h0, h13380, hlam]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [h13115, hlam, p13361_1]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [hlam, p13361_0]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [h12236, h12238, h13120, h13121, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13361_1]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [h12236, h12238, h13115, h13120, h13121, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13361_1]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        rcases p13361_3 (m.d 0 1) (by simp) with h13391 | h13391
                        · linarith only [h13391, hlam, p13361_0]
                        · rcases p13361_3 (m.d 1 2) (by simp) with h13393 | h13393
                          · rcases p13361_3 (m.d 1 3) (by simp) with h13394 | h13394
                            · rcases p13361_3 (m.d 1 4) (by simp) with h13395 | h13395
                              · rcases p13361_3 (m.d 1 5) (by simp) with h13396 | h13396
                                · linarith only [h13120, h13396, hlam]
                                · linarith only [h12013, h13396, hlam]
                              · linarith only [h13395, hlam, p13361_0]
                            · linarith only [h10472, h13394, hlam]
                          · linarith only [h0, h13393, hlam]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [h13116, hlam, p13361_1]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [h13118, hlam, p13361_0]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [hlam, p13361_0]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [h12236, h12238, h13120, h13121, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13361_1]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        rcases p13361_3 (m.d 0 1) (by simp) with h13406 | h13406
                        · linarith only [h13406, hlam, p13361_0]
                        · rcases p13361_3 (m.d 1 2) (by simp) with h13408 | h13408
                          · rcases p13361_3 (m.d 1 3) (by simp) with h13409 | h13409
                            · rcases p13361_3 (m.d 1 4) (by simp) with h13410 | h13410
                              · rcases p13361_3 (m.d 1 5) (by simp) with h13411 | h13411
                                · rcases h1emax with h13412 | h13412 | h13412 | h13412 | h13412
                                  · rcases h3bigk with h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c | h13413c
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      linarith only [hlam, p13413_0]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      linarith only [h10472, hlam, p13413_1]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      rcases p13413_3 (m.d 0 3) (by simp) with h13416 | h13416
                                      · rcases p13413_3 (m.d 1 3) (by simp) with h13417 | h13417
                                        · rcases p13413_3 (m.d 2 3) (by simp) with h13418 | h13418
                                          · linarith only [h12233, h13418, hlam]
                                          · rcases p13413_3 (m.d 3 4) (by simp) with h13420 | h13420
                                            · linarith only [h12236, h13420, hlam]
                                            · linarith only [h13121, h13420, hlam]
                                        · linarith only [h13115, h13417, hlam]
                                      · linarith only [h12233, h13416, hlam]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      rcases p13413_3 (m.d 0 3) (by simp) with h13425 | h13425
                                      · rcases p13413_3 (m.d 1 3) (by simp) with h13426 | h13426
                                        · rcases p13413_3 (m.d 2 3) (by simp) with h13427 | h13427
                                          · linarith only [h12233, h13427, hlam]
                                          · rcases p13413_3 (m.d 3 4) (by simp) with h13429 | h13429
                                            · linarith only [h13429, hlam, p13413_0]
                                            · rcases p13413_3 (m.d 3 5) (by simp) with h13431 | h13431
                                              · linarith only [h12237, h13431, hlam]
                                              · linarith only [h13359, h13431, hlam]
                                        · linarith only [h13118, h13426, hlam]
                                      · linarith only [h13425, hlam, p13413_0]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      rcases p13413_3 (m.d 0 3) (by simp) with h13436 | h13436
                                      · rcases p13413_3 (m.d 1 3) (by simp) with h13437 | h13437
                                        · rcases p13413_3 (m.d 2 3) (by simp) with h13438 | h13438
                                          · linarith only [h12233, h13438, hlam]
                                          · rcases p13413_3 (m.d 3 4) (by simp) with h13440 | h13440
                                            · linarith only [h12236, h13440, hlam]
                                            · rcases p13413_3 (m.d 3 5) (by simp) with h13442 | h13442
                                              · linarith only [h13442, hlam, p13413_0]
                                              · rcases h5bigk with h13444c | h13444c | h13444c | h13444c | h13444c | h13444c | h13444c | h13444c | h13444c | h13444c | h13444c | h13444c | h13444c | h13444c | h13444c | h13444c | h13444c | h13444c | h13444c | h13444c | h13444c | h13444c | h13444c | h13444c | h13444c
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [hlam, p13444_0]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [h12013, hlam, p13444_1]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [h12238, h13115, h13118, h13120, hc12, hlam, hphi, ht01, ht0b, ht5b, p13444_1, u5ehi2]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [h12238, h13115, h13118, h13120, hc12, hlam, hphi, ht01, ht0b, ht5b, p13444_1, u5ehi3]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [h12238, hlam, p13444_1]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  rcases p13444_3 (m.d 0 5) (by simp) with h13450 | h13450
                                                  · linarith only [h12013, h13450, hlam]
                                                  · rcases p13444_3 (m.d 1 5) (by simp) with h13452 | h13452
                                                    · rcases p13444_3 (m.d 2 5) (by simp) with h13453 | h13453
                                                      · linarith only [h13117, h13453, hlam]
                                                      · rcases p13444_3 (m.d 3 5) (by simp) with h13455 | h13455
                                                        · linarith only [h13119, h13455, hlam]
                                                        · rcases p13444_3 (m.d 4 5) (by simp) with h13457 | h13457
                                                          · linarith only [h13120, h13457, hlam]
                                                          · linarith only [h12238, h13457, hlam]
                                                    · linarith only [h12013, h13452, hlam]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [hlam, p13444_0]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  rcases p13444_3 (m.d 0 5) (by simp) with h13462 | h13462
                                                  · linarith only [h12013, h13462, hlam]
                                                  · linarith only [h12235, h13462, hlam]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  rcases p13444_3 (m.d 0 5) (by simp) with h13465 | h13465
                                                  · linarith only [h12013, h13465, hlam]
                                                  · linarith only [h12237, h13465, hlam]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [h12236, h12238, h13115, h13118, h13120, h13121, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13444_1]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [h12235, hlam, p13444_1]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [h13117, hlam, p13444_1]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [hlam, p13444_0]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [h13355, hlam, p13444_1]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [h13357, hlam, p13444_1]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [h12237, hlam, p13444_0]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [h13119, hlam, p13444_0]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [h10472, h13115, hc12, hlam, hphi, ht01, ht0b, ht5b, p13413_1, p13444_1, u5ehi2]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [hlam, p13444_0]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [h13359, hlam, p13444_1]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [h12236, h12238, h13121, hc23, hc45, hlam, hphi, ht34, p13444_1]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [h13120, hlam, p13444_0]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [h13115, h13118, h13120, hc12, hlam, hphi, ht01, ht0b, ht5b, p13444_1, u5ehi2]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [h13115, h13118, h13120, h13355, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13444_1]
                                                · have p13444_0 := h13444c.1
                                                  have p13444_1 := h13444c.2.1
                                                  have p13444_2 := h13444c.2.2.1
                                                  have p13444_3 := h13444c.2.2.2
                                                  linarith only [hlam, p13444_0]
                                        · linarith only [h13119, h13437, hlam]
                                      · linarith only [h13436, hlam, p13413_0]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      linarith only [h12236, h13115, h13121, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13413_1]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      linarith only [hlam, p13413_0]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      linarith only [h12236, h12238, h13118, h13120, h13121, hlam, p13413_2]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      rcases p13413_3 (m.d 0 3) (by simp) with h13489 | h13489
                                      · linarith only [h10472, h13489, hlam]
                                      · linarith only [h12236, h13489, hlam]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      rcases p13413_3 (m.d 0 3) (by simp) with h13492 | h13492
                                      · linarith only [h10472, h13492, hlam]
                                      · linarith only [h12237, h13492, hlam]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      linarith only [h12233, hlam, p13413_0]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      linarith only [h13115, hlam, p13413_0]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      linarith only [hlam, p13413_0]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      linarith only [h13121, hlam, p13413_0]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      linarith only [h13355, hlam, p13413_0]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      linarith only [h12236, hlam, p13413_0]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      linarith only [h13118, hlam, p13413_0]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      linarith only [h12236, h12238, h13118, h13120, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13413_1]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      linarith only [hlam, p13413_0]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      linarith only [h13359, hlam, p13413_1]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      linarith only [h12237, hlam, p13413_0]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      linarith only [h13119, hlam, p13413_0]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      rcases p13413_3 (m.d 0 3) (by simp) with h13507 | h13507
                                      · rcases p13413_3 (m.d 1 3) (by simp) with h13508 | h13508
                                        · rcases p13413_3 (m.d 2 3) (by simp) with h13509 | h13509
                                          · linarith only [h13509, hlam, p13413_0]
                                          · rcases p13413_3 (m.d 3 4) (by simp) with h13511 | h13511
                                            · linarith only [h13359, h13511, hlam]
                                            · linarith only [h13121, h13511, hlam]
                                        · linarith only [h13115, h13508, hlam]
                                      · linarith only [h12233, h13507, hlam]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      linarith only [h12237, h13121, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p13413_1]
                                    · have p13413_0 := h13413c.1
                                      have p13413_1 := h13413c.2.1
                                      have p13413_2 := h13413c.2.2.1
                                      have p13413_3 := h13413c.2.2.2
                                      linarith only [hlam, p13413_0]
                                  · linarith only [h12238, h13115, h13118, h13120, h13412, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h12236, h12238, h13118, h13120, h13121, h13412, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                  · linarith only [h12236, h12238, h13120, h13121, h13412, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                  · linarith only [h13412, hc01, hlam, p13361_1]
                                · linarith only [h13411, hlam, p13361_0]
                              · linarith only [h11379, h13410, hlam]
                            · linarith only [h10472, h13409, hlam]
                          · linarith only [h0, h13408, hlam]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [h13117, hlam, p13361_1]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [h13119, hlam, p13361_0]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [h13120, hlam, p13361_0]
                      · have p13361_0 := h13361c.1
                        have p13361_1 := h13361c.2.1
                        have p13361_2 := h13361c.2.2.1
                        have p13361_3 := h13361c.2.2.2
                        linarith only [hlam, p13361_0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h13530 | h13530
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13531 | h13531
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13532 | h13532
                  · linarith only [h11379, h13120, h13532, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13534 | h13534
                    · linarith only [h11379, h12233, h13120, h13530, h13534, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                    · rcases h1bigk with h13536c | h13536c | h13536c | h13536c | h13536c | h13536c | h13536c | h13536c | h13536c | h13536c | h13536c | h13536c | h13536c | h13536c | h13536c | h13536c | h13536c | h13536c | h13536c | h13536c | h13536c | h13536c | h13536c | h13536c | h13536c
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [hlam, p13536_0]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [h0, hlam, p13536_0]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [h10472, hlam, p13536_0]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [h11379, hlam, p13536_0]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [h12013, hlam, p13536_0]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        rcases p13536_3 (m.d 0 1) (by simp) with h13542 | h13542
                        · linarith only [h13542, hlam, p13536_0]
                        · rcases p13536_3 (m.d 1 2) (by simp) with h13544 | h13544
                          · rcases p13536_3 (m.d 1 3) (by simp) with h13545 | h13545
                            · linarith only [h13115, h13545, hlam]
                            · linarith only [h10472, h13545, hlam]
                          · linarith only [h13544, hlam, p13536_0]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [hlam, p13536_0]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [h10472, hc01, hc12, hlam, hphi, p13536_1]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [h11379, hc01, hc12, hlam, hphi, p13536_1]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [h11379, h13120, hc01, hc12, hlam, hphi, p13536_1]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        rcases p13536_3 (m.d 0 1) (by simp) with h13553 | h13553
                        · linarith only [h13553, hlam, p13536_0]
                        · rcases p13536_3 (m.d 1 2) (by simp) with h13555 | h13555
                          · rcases p13536_3 (m.d 1 3) (by simp) with h13556 | h13556
                            · rcases p13536_3 (m.d 1 4) (by simp) with h13557 | h13557
                              · linarith only [h13118, h13557, hlam]
                              · linarith only [h11379, h13557, hlam]
                            · linarith only [h13556, hlam, p13536_0]
                          · linarith only [h0, h13555, hlam]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [h13115, hlam, p13536_1]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [hlam, p13536_0]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [h11379, hc01, hc13, hlam, hphi, p13536_1]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [h11379, h13115, h13120, hc01, hc12, hlam, hphi, p13536_1]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [h13120, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13536_1]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [h13116, hlam, p13536_1]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [h13118, hlam, p13536_0]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [hlam, p13536_0]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [h13120, hlam, p13536_1]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        rcases p13536_3 (m.d 0 1) (by simp) with h13571 | h13571
                        · linarith only [h13571, hlam, p13536_0]
                        · rcases p13536_3 (m.d 1 2) (by simp) with h13573 | h13573
                          · rcases p13536_3 (m.d 1 3) (by simp) with h13574 | h13574
                            · rcases p13536_3 (m.d 1 4) (by simp) with h13575 | h13575
                              · linarith only [h13120, h13575, hlam]
                              · linarith only [h11379, h13575, hlam]
                            · linarith only [h10472, h13574, hlam]
                          · linarith only [h0, h13573, hlam]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [h13117, hlam, p13536_1]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [h13119, hlam, p13536_0]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [h11379, hc01, hc15, hlam, hphi, p13536_1]
                      · have p13536_0 := h13536c.1
                        have p13536_1 := h13536c.2.1
                        have p13536_2 := h13536c.2.2.1
                        have p13536_3 := h13536c.2.2.2
                        linarith only [hlam, p13536_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13584 | h13584
                  · linarith only [h0, h12013, h12233, h12237, h13120, h13530, h13531, h13584, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13586 | h13586
                    · linarith only [h0, h12013, h12233, h12236, h13120, h13586, hc01, hc12, hlam, hphi]
                    · rcases h1bigk with h13588c | h13588c | h13588c | h13588c | h13588c | h13588c | h13588c | h13588c | h13588c | h13588c | h13588c | h13588c | h13588c | h13588c | h13588c | h13588c | h13588c | h13588c | h13588c | h13588c | h13588c | h13588c | h13588c | h13588c | h13588c
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [hlam, p13588_0]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [h0, hlam, p13588_0]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [h10472, hlam, p13588_0]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [h11379, hlam, p13588_0]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [h12013, hlam, p13588_0]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        rcases p13588_3 (m.d 0 1) (by simp) with h13594 | h13594
                        · linarith only [h13594, hlam, p13588_0]
                        · rcases p13588_3 (m.d 1 2) (by simp) with h13596 | h13596
                          · rcases p13588_3 (m.d 1 3) (by simp) with h13597 | h13597
                            · linarith only [h13115, h13597, hlam]
                            · linarith only [h10472, h13597, hlam]
                          · linarith only [h13596, hlam, p13588_0]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [hlam, p13588_0]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [h10472, hc01, hc12, hlam, hphi, p13588_1]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [h11379, hc01, hc12, hlam, hphi, p13588_1]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [h12013, h12237, h13530, h13531, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13588_1]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        rcases p13588_3 (m.d 0 1) (by simp) with h13605 | h13605
                        · linarith only [h13605, hlam, p13588_0]
                        · rcases p13588_3 (m.d 1 2) (by simp) with h13607 | h13607
                          · rcases p13588_3 (m.d 1 3) (by simp) with h13608 | h13608
                            · rcases p13588_3 (m.d 1 4) (by simp) with h13609 | h13609
                              · linarith only [h13118, h13609, hlam]
                              · linarith only [h11379, h13609, hlam]
                            · linarith only [h13608, hlam, p13588_0]
                          · linarith only [h0, h13607, hlam]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [h13115, hlam, p13588_1]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [hlam, p13588_0]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [h11379, hc01, hc13, hlam, hphi, p13588_1]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [h12013, h12237, h13115, h13530, h13531, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13588_1]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [h13120, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13588_1]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [h13116, hlam, p13588_1]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [h13118, hlam, p13588_0]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [hlam, p13588_0]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [h13120, hlam, p13588_1]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        rcases p13588_3 (m.d 0 1) (by simp) with h13623 | h13623
                        · linarith only [h13623, hlam, p13588_0]
                        · rcases p13588_3 (m.d 1 2) (by simp) with h13625 | h13625
                          · rcases p13588_3 (m.d 1 3) (by simp) with h13626 | h13626
                            · rcases p13588_3 (m.d 1 4) (by simp) with h13627 | h13627
                              · linarith only [h13120, h13627, hlam]
                              · linarith only [h11379, h13627, hlam]
                            · linarith only [h10472, h13626, hlam]
                          · linarith only [h0, h13625, hlam]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [h13117, hlam, p13588_1]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [h13119, hlam, p13588_0]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [h11379, hc01, hc15, hlam, hphi, p13588_1]
                      · have p13588_0 := h13588c.1
                        have p13588_1 := h13588c.2.1
                        have p13588_2 := h13588c.2.2.1
                        have p13588_3 := h13588c.2.2.2
                        linarith only [hlam, p13588_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h13636 | h13636
                · linarith only [h12236, h13530, h13636, hc03, hlam, hphi, ht0b, ht5b, u5ehi3]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h13638 | h13638
                  · linarith only [h0, h12013, h12234, h13120, h13638, hc01, hc12, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h13640 | h13640
                    · linarith only [h11379, h12236, h13120, h13640, hlam]
                    · rcases h1bigk with h13642c | h13642c | h13642c | h13642c | h13642c | h13642c | h13642c | h13642c | h13642c | h13642c | h13642c | h13642c | h13642c | h13642c | h13642c | h13642c | h13642c | h13642c | h13642c | h13642c | h13642c | h13642c | h13642c | h13642c | h13642c
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [hlam, p13642_0]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [h0, hlam, p13642_0]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [h10472, hlam, p13642_0]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [h11379, hlam, p13642_0]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [h12013, hlam, p13642_0]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        rcases p13642_3 (m.d 0 1) (by simp) with h13648 | h13648
                        · linarith only [h13648, hlam, p13642_0]
                        · rcases p13642_3 (m.d 1 2) (by simp) with h13650 | h13650
                          · rcases p13642_3 (m.d 1 3) (by simp) with h13651 | h13651
                            · linarith only [h13115, h13651, hlam]
                            · linarith only [h10472, h13651, hlam]
                          · linarith only [h13650, hlam, p13642_0]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [hlam, p13642_0]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [h10472, hc01, hc12, hlam, hphi, p13642_1]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [h11379, hc01, hc12, hlam, hphi, p13642_1]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [h12013, hc01, hc12, hlam, hphi, p13642_1]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        rcases p13642_3 (m.d 0 1) (by simp) with h13659 | h13659
                        · linarith only [h13659, hlam, p13642_0]
                        · rcases p13642_3 (m.d 1 2) (by simp) with h13661 | h13661
                          · rcases p13642_3 (m.d 1 3) (by simp) with h13662 | h13662
                            · rcases p13642_3 (m.d 1 4) (by simp) with h13663 | h13663
                              · linarith only [h13118, h13663, hlam]
                              · linarith only [h11379, h13663, hlam]
                            · linarith only [h13662, hlam, p13642_0]
                          · linarith only [h0, h13661, hlam]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [h13115, hlam, p13642_1]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [hlam, p13642_0]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [h11379, hc01, hc13, hlam, hphi, p13642_1]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [h12013, h13115, hc01, hc12, hlam, hphi, p13642_1]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [h13120, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13642_1]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [h13116, hlam, p13642_1]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [h13118, hlam, p13642_0]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [hlam, p13642_0]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [h13120, hlam, p13642_1]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        rcases p13642_3 (m.d 0 1) (by simp) with h13677 | h13677
                        · linarith only [h13677, hlam, p13642_0]
                        · rcases p13642_3 (m.d 1 2) (by simp) with h13679 | h13679
                          · rcases p13642_3 (m.d 1 3) (by simp) with h13680 | h13680
                            · rcases p13642_3 (m.d 1 4) (by simp) with h13681 | h13681
                              · linarith only [h13120, h13681, hlam]
                              · linarith only [h11379, h13681, hlam]
                            · linarith only [h10472, h13680, hlam]
                          · linarith only [h0, h13679, hlam]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [h13117, hlam, p13642_1]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [h13119, hlam, p13642_0]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [h11379, hc01, hc15, hlam, hphi, p13642_1]
                      · have p13642_0 := h13642c.1
                        have p13642_1 := h13642c.2.1
                        have p13642_2 := h13642c.2.2.1
                        have p13642_3 := h13642c.2.2.2
                        linarith only [hlam, p13642_0]
          · linarith only [h10472, h12237, h13119, hlam]
        · linarith only [h10472, h12236, h13118, hlam]
      · linarith only [h0, h12235, h13117, hlam]
    · linarith only [h0, h12234, h12238, h13116, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
  · linarith only [h0, h12233, h13115, hlam]

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h12237 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  rcases m.htr 0 4 5 (by decide) (by decide) with h12238 | h12238
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x0 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236 h12237 h12238
  · exact r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x0_x1 m hb1 hb3 hb5 hg0 hg10472 hg11379 hg12013 hg12233 h12234 h12235 h12236 h12237 h12238

set_option maxHeartbeats 5420000 in
set_option maxHeartbeats 5420000 in
theorem r1l7_11_13_25_L_I_L_I_M_IR_s16_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg10472 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg11379 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg12013 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (hg12233 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h12234 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h12235 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h12236 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h12237 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1emax := hb1.2.2
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have h5bigk := hb5.2.2.2
  have u5ehi0 := h5ehi (m.d 0 5) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  have h0 := hg0
  have h10472 := hg10472
  have h11379 := hg11379
  have h12013 := hg12013
  have h12233 := hg12233
  rcases m.htr 0 4 5 (by decide) (by decide) with h13695 | h13695
  · linarith only [h12236, h12237, h13695, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h13697 | h13697
    · rcases m.htr 1 2 4 (by decide) (by decide) with h13698 | h13698
      · rcases m.htr 1 2 5 (by decide) (by decide) with h13699 | h13699
        · rcases m.htr 1 3 4 (by decide) (by decide) with h13700 | h13700
          · rcases m.htr 1 3 5 (by decide) (by decide) with h13701 | h13701
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13702 | h13702
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13703 | h13703
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13704 | h13704
                  · linarith only [h12233, h12237, h13704, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13706 | h13706
                    · linarith only [h12234, h13695, h13706, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13708 | h13708
                      · linarith only [h12233, h12237, h13695, h13697, h13701, h13703, h13708, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases h1bigk with h13710c | h13710c | h13710c | h13710c | h13710c | h13710c | h13710c | h13710c | h13710c | h13710c | h13710c | h13710c | h13710c | h13710c | h13710c | h13710c | h13710c | h13710c | h13710c | h13710c | h13710c | h13710c | h13710c | h13710c | h13710c
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [hlam, p13710_0]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [h0, hlam, p13710_0]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [h10472, hlam, p13710_0]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [h11379, hlam, p13710_0]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [h12013, hlam, p13710_0]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          rcases p13710_3 (m.d 0 1) (by simp) with h13716 | h13716
                          · linarith only [h13716, hlam, p13710_0]
                          · rcases p13710_3 (m.d 1 2) (by simp) with h13718 | h13718
                            · rcases p13710_3 (m.d 1 3) (by simp) with h13719 | h13719
                              · linarith only [h13697, h13719, hlam]
                              · linarith only [h10472, h13719, hlam]
                            · linarith only [h13718, hlam, p13710_0]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [hlam, p13710_0]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [h12237, h13700, h13702, h13708, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13710_1]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [h12236, h12237, h13702, h13708, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13710_1]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [h12013, hc01, hc12, hlam, hphi, p13710_1]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          rcases p13710_3 (m.d 0 1) (by simp) with h13727 | h13727
                          · linarith only [h13727, hlam, p13710_0]
                          · rcases p13710_3 (m.d 1 2) (by simp) with h13729 | h13729
                            · rcases p13710_3 (m.d 1 3) (by simp) with h13730 | h13730
                              · rcases p13710_3 (m.d 1 4) (by simp) with h13731 | h13731
                                · linarith only [h13700, h13731, hlam]
                                · linarith only [h11379, h13731, hlam]
                              · linarith only [h13730, hlam, p13710_0]
                            · linarith only [h0, h13729, hlam]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [h13697, hlam, p13710_1]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [hlam, p13710_0]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [h12233, h12237, h13702, h13703, h13708, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13710_1]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [h12233, h12237, h13697, h13702, h13703, h13708, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13710_1]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          rcases p13710_3 (m.d 0 1) (by simp) with h13740 | h13740
                          · linarith only [h13740, hlam, p13710_0]
                          · rcases p13710_3 (m.d 1 2) (by simp) with h13742 | h13742
                            · rcases p13710_3 (m.d 1 3) (by simp) with h13743 | h13743
                              · rcases p13710_3 (m.d 1 4) (by simp) with h13744 | h13744
                                · rcases p13710_3 (m.d 1 5) (by simp) with h13745 | h13745
                                  · linarith only [h13702, h13745, hlam]
                                  · linarith only [h12013, h13745, hlam]
                                · linarith only [h13744, hlam, p13710_0]
                              · linarith only [h10472, h13743, hlam]
                            · linarith only [h0, h13742, hlam]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [h13698, hlam, p13710_1]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [h13700, hlam, p13710_0]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [hlam, p13710_0]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [h12233, h12237, h13702, h13703, h13708, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13710_1]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          rcases p13710_3 (m.d 0 1) (by simp) with h13755 | h13755
                          · linarith only [h13755, hlam, p13710_0]
                          · rcases p13710_3 (m.d 1 2) (by simp) with h13757 | h13757
                            · rcases p13710_3 (m.d 1 3) (by simp) with h13758 | h13758
                              · rcases p13710_3 (m.d 1 4) (by simp) with h13759 | h13759
                                · rcases p13710_3 (m.d 1 5) (by simp) with h13760 | h13760
                                  · rcases h1emax with h13761 | h13761 | h13761 | h13761 | h13761
                                    · rcases h3bigk with h13762c | h13762c | h13762c | h13762c | h13762c | h13762c | h13762c | h13762c | h13762c | h13762c | h13762c | h13762c | h13762c | h13762c | h13762c | h13762c | h13762c | h13762c | h13762c | h13762c | h13762c | h13762c | h13762c | h13762c | h13762c
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [hlam, p13762_0]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [h10472, hlam, p13762_1]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [h12237, h13703, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p13762_1]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [h12237, h13708, hc34, hc45, hlam, hphi, p13762_1]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [h12237, hlam, p13762_0]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        rcases p13762_3 (m.d 0 3) (by simp) with h13768 | h13768
                                        · linarith only [h10472, h13768, hlam]
                                        · rcases p13762_3 (m.d 1 3) (by simp) with h13770 | h13770
                                          · rcases p13762_3 (m.d 2 3) (by simp) with h13771 | h13771
                                            · linarith only [h13697, h13771, hlam]
                                            · rcases p13762_3 (m.d 3 4) (by simp) with h13773 | h13773
                                              · linarith only [h13700, h13773, hlam]
                                              · rcases p13762_3 (m.d 3 5) (by simp) with h13775 | h13775
                                                · linarith only [h13701, h13775, hlam]
                                                · linarith only [h12237, h13775, hlam]
                                          · linarith only [h10472, h13770, hlam]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [hlam, p13762_0]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        rcases p13762_3 (m.d 0 3) (by simp) with h13780 | h13780
                                        · linarith only [h10472, h13780, hlam]
                                        · linarith only [h12233, h13780, hlam]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [h12233, h12237, h13700, h13702, h13703, h13708, hlam, p13762_2]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [h12233, h12237, h13697, h13703, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13762_1]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [h12233, hlam, p13762_0]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [h13697, hlam, p13762_0]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [hlam, p13762_0]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [h12233, h12237, h13708, hc34, hc45, hlam, hphi, p13762_1]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [h13704, hlam, p13762_0]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [h12236, hlam, p13762_0]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [h13700, hlam, p13762_0]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [h13703, hlam, p13762_0]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [hlam, p13762_0]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [h13708, hlam, p13762_1]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [h12236, h13708, hc34, hc45, hlam, hphi, p13762_1]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [h13701, hlam, p13762_0]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [h13697, h13701, h13703, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13762_1]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        rcases p13762_3 (m.d 0 3) (by simp) with h13798 | h13798
                                        · linarith only [h12237, h13798, hlam]
                                        · linarith only [h12236, h13798, hlam]
                                      · have p13762_0 := h13762c.1
                                        have p13762_1 := h13762c.2.1
                                        have p13762_2 := h13762c.2.2.1
                                        have p13762_3 := h13762c.2.2.2
                                        linarith only [hlam, p13762_0]
                                    · linarith only [h13697, h13700, h13702, h13708, h13761, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
                                    · linarith only [h12233, h12237, h13700, h13702, h13703, h13708, h13761, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · linarith only [h12233, h12237, h13702, h13703, h13708, h13761, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                    · linarith only [h13761, hc01, hlam, p13710_1]
                                  · linarith only [h13760, hlam, p13710_0]
                                · linarith only [h11379, h13759, hlam]
                              · linarith only [h10472, h13758, hlam]
                            · linarith only [h0, h13757, hlam]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [h13699, hlam, p13710_1]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [h13701, hlam, p13710_0]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [h13702, hlam, p13710_0]
                        · have p13710_0 := h13710c.1
                          have p13710_1 := h13710c.2.1
                          have p13710_2 := h13710c.2.2.1
                          have p13710_3 := h13710c.2.2.2
                          linarith only [hlam, p13710_0]
                · linarith only [h12236, h12237, h13703, hc23, hc35, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13815 | h13815
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13816 | h13816
                  · linarith only [h12233, h12237, h13816, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13818 | h13818
                    · linarith only [h11379, h13702, h13818, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13820 | h13820
                      · linarith only [h12233, h12237, h13697, h13701, h13702, h13815, h13820, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                      · rcases h1bigk with h13822c | h13822c | h13822c | h13822c | h13822c | h13822c | h13822c | h13822c | h13822c | h13822c | h13822c | h13822c | h13822c | h13822c | h13822c | h13822c | h13822c | h13822c | h13822c | h13822c | h13822c | h13822c | h13822c | h13822c | h13822c
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [hlam, p13822_0]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [h0, hlam, p13822_0]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [h10472, hlam, p13822_0]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [h11379, hlam, p13822_0]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [h12013, hlam, p13822_0]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          rcases p13822_3 (m.d 0 1) (by simp) with h13828 | h13828
                          · linarith only [h13828, hlam, p13822_0]
                          · rcases p13822_3 (m.d 1 2) (by simp) with h13830 | h13830
                            · rcases p13822_3 (m.d 1 3) (by simp) with h13831 | h13831
                              · linarith only [h13697, h13831, hlam]
                              · linarith only [h10472, h13831, hlam]
                            · linarith only [h13830, hlam, p13822_0]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [hlam, p13822_0]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [h12237, h13701, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p13822_1]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [h11379, hc01, hc12, hlam, hphi, p13822_1]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [h12233, h12237, h13701, h13815, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13822_1]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          rcases p13822_3 (m.d 0 1) (by simp) with h13839 | h13839
                          · linarith only [h13839, hlam, p13822_0]
                          · rcases p13822_3 (m.d 1 2) (by simp) with h13841 | h13841
                            · rcases p13822_3 (m.d 1 3) (by simp) with h13842 | h13842
                              · rcases p13822_3 (m.d 1 4) (by simp) with h13843 | h13843
                                · linarith only [h13700, h13843, hlam]
                                · linarith only [h11379, h13843, hlam]
                              · linarith only [h13842, hlam, p13822_0]
                            · linarith only [h0, h13841, hlam]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [h13697, hlam, p13822_1]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [hlam, p13822_0]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [h11379, hc01, hc13, hlam, hphi, p13822_1]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [h12233, h12237, h13697, h13701, h13815, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p13822_1]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [h13702, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13822_1]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [h13698, hlam, p13822_1]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [h13700, hlam, p13822_0]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [hlam, p13822_0]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [h13702, hlam, p13822_1]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          rcases p13822_3 (m.d 0 1) (by simp) with h13857 | h13857
                          · linarith only [h13857, hlam, p13822_0]
                          · rcases p13822_3 (m.d 1 2) (by simp) with h13859 | h13859
                            · rcases p13822_3 (m.d 1 3) (by simp) with h13860 | h13860
                              · rcases p13822_3 (m.d 1 4) (by simp) with h13861 | h13861
                                · linarith only [h13702, h13861, hlam]
                                · linarith only [h11379, h13861, hlam]
                              · linarith only [h10472, h13860, hlam]
                            · linarith only [h0, h13859, hlam]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [h13699, hlam, p13822_1]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [h13701, hlam, p13822_0]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [h11379, hc01, hc15, hlam, hphi, p13822_1]
                        · have p13822_0 := h13822c.1
                          have p13822_1 := h13822c.2.1
                          have p13822_2 := h13822c.2.2.1
                          have p13822_3 := h13822c.2.2.2
                          linarith only [hlam, p13822_0]
                · linarith only [h12236, h12237, h13815, hc23, hc35, hlam, hphi]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h13871 | h13871
              · linarith only [h11379, h13695, h13700, h13701, h13871, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h13873 | h13873
                · rcases m.htr 2 3 5 (by decide) (by decide) with h13874 | h13874
                  · linarith only [h10472, h13701, h13874, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h13876 | h13876
                    · linarith only [h0, h12013, h12234, h13871, h13876, hc01, hc12, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h13878 | h13878
                      · linarith only [h11379, h13871, h13878, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases h1bigk with h13880c | h13880c | h13880c | h13880c | h13880c | h13880c | h13880c | h13880c | h13880c | h13880c | h13880c | h13880c | h13880c | h13880c | h13880c | h13880c | h13880c | h13880c | h13880c | h13880c | h13880c | h13880c | h13880c | h13880c | h13880c
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [hlam, p13880_0]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [h0, hlam, p13880_0]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [h10472, hlam, p13880_0]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [h11379, hlam, p13880_0]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [h12013, hlam, p13880_0]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          rcases p13880_3 (m.d 0 1) (by simp) with h13886 | h13886
                          · linarith only [h13886, hlam, p13880_0]
                          · rcases p13880_3 (m.d 1 2) (by simp) with h13888 | h13888
                            · rcases p13880_3 (m.d 1 3) (by simp) with h13889 | h13889
                              · linarith only [h13697, h13889, hlam]
                              · linarith only [h10472, h13889, hlam]
                            · linarith only [h13888, hlam, p13880_0]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [hlam, p13880_0]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [h11379, h13700, hc01, hc12, hlam, hphi, p13880_1]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [h11379, hc01, hc12, hlam, hphi, p13880_1]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [h12013, hc01, hc12, hlam, hphi, p13880_1]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [h13701, hc01, hc35, hlam, hphi, ht12, ht23, p13880_1]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [h13697, hlam, p13880_1]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [hlam, p13880_0]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [h11379, h13701, h13878, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13880_1]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [h13701, hlam, p13880_1]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [h13700, h13701, h13878, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13880_1]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [h13698, hlam, p13880_1]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [h13700, hlam, p13880_0]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [hlam, p13880_0]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [h13871, hlam, p13880_1]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          rcases p13880_3 (m.d 0 1) (by simp) with h13907 | h13907
                          · linarith only [h13907, hlam, p13880_0]
                          · rcases p13880_3 (m.d 1 2) (by simp) with h13909 | h13909
                            · rcases p13880_3 (m.d 1 3) (by simp) with h13910 | h13910
                              · linarith only [h13701, h13910, hlam]
                              · linarith only [h10472, h13910, hlam]
                            · linarith only [h0, h13909, hlam]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [h13699, hlam, p13880_1]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [h10472, hc01, hc15, hlam, hphi, p13880_1]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [h11379, h13701, h13878, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p13880_1]
                        · have p13880_0 := h13880c.1
                          have p13880_1 := h13880c.2.1
                          have p13880_2 := h13880c.2.2.1
                          have p13880_3 := h13880c.2.2.2
                          linarith only [hlam, p13880_0]
                · linarith only [h12236, h12237, h13873, hc23, hc35, hlam, hphi]
          · linarith only [h10472, h12236, h13700, hlam]
        · linarith only [h0, h12235, h13699, hlam]
      · linarith only [h0, h12234, h13698, hlam]
    · linarith only [h0, h12233, h13697, hlam]

end R2N4
