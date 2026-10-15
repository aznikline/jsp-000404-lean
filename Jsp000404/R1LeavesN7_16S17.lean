import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10428000 in
set_option maxHeartbeats 10428000 in
theorem r1l7_21_15_H_I_L_I_s7_x0_x0 (m : N7Model)
    (hb1 : CMSig2_7_H_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h6137 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h6138 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h6139 | h6139
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6140 | h6140
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6141 | h6141
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6142 | h6142
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6143 | h6143
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6144 | h6144
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6145 | h6145
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6146 | h6146
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6147 | h6147
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6148 | h6148
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6149 | h6149
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6150 | h6150
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6151 | h6151
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6152 | h6152
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6153 | h6153
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6154 | h6154
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6155 | h6155
                                  · linarith only [h0, h6137, h6146, h6152, h6155, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                  · linarith only [h0, h6137, h6149, h6151, h6155, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                · linarith only [h0, h6137, h6149, h6151, h6154, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h0, h6137, h6150, h6153, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h0, h6137, h6149, h6152, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6161 | h6161
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6162 | h6162
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6163 | h6163
                                · linarith only [h6147, h6151, h6163, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6165 | h6165
                                  · linarith only [h6147, h6151, h6161, h6165, hlam]
                                  · rcases h1bigk with h6167c | h6167c | h6167c | h6167c | h6167c | h6167c | h6167c | h6167c | h6167c | h6167c | h6167c | h6167c | h6167c | h6167c | h6167c | h6167c | h6167c | h6167c | h6167c | h6167c | h6167c | h6167c | h6167c | h6167c | h6167c
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [hlam, p6167_0]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [h0, hlam, p6167_0]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [h0, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6167_1]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [h0, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p6167_1]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6167_1]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p6167_1]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [hlam, p6167_0]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [h6146, h6162, h6165, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6167_1]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      rcases p6167_3 (m.d 0 1) (by simp) with h6176 | h6176
                                      · linarith only [h0, h6176, hlam]
                                      · linarith only [h6138, h6176, hlam]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      rcases p6167_3 (m.d 0 1) (by simp) with h6179 | h6179
                                      · linarith only [h0, h6179, hlam]
                                      · linarith only [h6139, h6179, hlam]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [h6137, hlam, p6167_0]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [h6146, hlam, p6167_1]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [hlam, p6167_0]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [h0, h6137, h6147, h6161, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6167_1]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [h0, h6137, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6167_1]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [h6138, hlam, p6167_0]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [h6147, hlam, p6167_1]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [h6149, hlam, p6167_0]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [hlam, p6167_0]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [h6151, hlam, p6167_1]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [h6139, hlam, p6167_0]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [h6148, hlam, p6167_1]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [h6150, hlam, p6167_0]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [h0, h6139, h6147, h6161, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6167_1]
                                    · have p6167_0 := h6167c.1
                                      have p6167_1 := h6167c.2.1
                                      have p6167_2 := h6167c.2.2.1
                                      have p6167_3 := h6167c.2.2.2
                                      linarith only [hlam, p6167_0]
                              · linarith only [h0, h6137, h6150, h6162, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h0, h6137, h6149, h6161, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h6137, h6144, h6149, h6150, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6200 | h6200
                        · linarith only [h0, h6137, h6143, h6149, h6200, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6202 | h6202
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6203 | h6203
                            · linarith only [h0, h6137, h6146, h6149, h6202, h6203, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6205 | h6205
                              · linarith only [h0, h6137, h6143, h6146, h6149, h6205, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6207 | h6207
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6208 | h6208
                                  · rcases h1bigk with h6209c | h6209c | h6209c | h6209c | h6209c | h6209c | h6209c | h6209c | h6209c | h6209c | h6209c | h6209c | h6209c | h6209c | h6209c | h6209c | h6209c | h6209c | h6209c | h6209c | h6209c | h6209c | h6209c | h6209c | h6209c
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [hlam, p6209_0]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [h0, hlam, p6209_0]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [h0, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6209_1]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [h0, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p6209_1]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6209_1]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p6209_1]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [hlam, p6209_0]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      rcases p6209_3 (m.d 0 1) (by simp) with h6217 | h6217
                                      · linarith only [h0, h6217, hlam]
                                      · linarith only [h6137, h6217, hlam]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [h6147, h6207, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6209_1]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      rcases p6209_3 (m.d 0 1) (by simp) with h6221 | h6221
                                      · linarith only [h0, h6221, hlam]
                                      · linarith only [h6139, h6221, hlam]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [h6137, hlam, p6209_0]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [h6146, hlam, p6209_1]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [hlam, p6209_0]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [h6149, hlam, p6209_1]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [h6200, hlam, p6209_1]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [h6138, hlam, p6209_0]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [h6147, hlam, p6209_1]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [h6138, h6146, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6209_1]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [hlam, p6209_0]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [h6143, h6148, h6149, h6205, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6209_1]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [h6139, hlam, p6209_0]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [h6148, hlam, p6209_1]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [h0, h6139, h6146, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6209_1]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [h6202, hlam, p6209_0]
                                    · have p6209_0 := h6209c.1
                                      have p6209_1 := h6209c.2.1
                                      have p6209_2 := h6209c.2.2.1
                                      have p6209_3 := h6209c.2.2.2
                                      linarith only [hlam, p6209_0]
                                  · linarith only [h6147, h6149, h6207, h6208, hlam]
                                · linarith only [h0, h6138, h6202, h6207, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6241 | h6241
                            · linarith only [h6146, h6149, h6241, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6243 | h6243
                              · linarith only [h0, h6137, h6143, h6145, h6146, h6149, h6202, h6243, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6245 | h6245
                                · linarith only [h6147, h6202, h6245, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6247 | h6247
                                  · linarith only [h0, h6137, h6143, h6202, h6247, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · linarith only [h0, h6137, h6143, h6145, h6146, h6149, h6247, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h6142, h6148, hlam]
                  · linarith only [h0, h6141, h6147, hlam]
                · linarith only [h0, h6140, h6146, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6253 | h6253
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6254 | h6254
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6255 | h6255
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6256 | h6256
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6257 | h6257
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6258 | h6258
                          · linarith only [h0, h6138, h6145, h6258, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6260 | h6260
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6261 | h6261
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6262 | h6262
                                · linarith only [h6138, h6145, h6254, h6262, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6264 | h6264
                                  · linarith only [h0, h6137, h6143, h6145, h6264, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                                  · rcases h1bigk with h6266c | h6266c | h6266c | h6266c | h6266c | h6266c | h6266c | h6266c | h6266c | h6266c | h6266c | h6266c | h6266c | h6266c | h6266c | h6266c | h6266c | h6266c | h6266c | h6266c | h6266c | h6266c | h6266c | h6266c | h6266c
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [hlam, p6266_0]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [h0, hlam, p6266_0]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [h0, h6253, h6261, h6264, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6266_1]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [h0, h6254, h6260, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6266_1]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [h0, h6254, h6258, h6260, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6266_1]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p6266_1]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [hlam, p6266_0]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [h6253, h6261, h6264, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6266_1]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      rcases p6266_3 (m.d 0 1) (by simp) with h6275 | h6275
                                      · linarith only [h0, h6275, hlam]
                                      · linarith only [h6138, h6275, hlam]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      rcases p6266_3 (m.d 0 1) (by simp) with h6278 | h6278
                                      · linarith only [h0, h6278, hlam]
                                      · linarith only [h6139, h6278, hlam]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [h6137, hlam, p6266_0]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [h6253, hlam, p6266_1]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [hlam, p6266_0]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [h6137, h6254, h6260, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6266_1]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [h0, h6137, h6254, h6258, h6260, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6266_1]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [h6138, hlam, p6266_0]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [h6254, hlam, p6266_1]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [h6256, hlam, p6266_0]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [hlam, p6266_0]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [h6258, hlam, p6266_1]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [h6139, hlam, p6266_0]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [h6255, hlam, p6266_1]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [h6257, hlam, p6266_0]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [h0, h6139, h6254, h6260, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6266_1]
                                    · have p6266_0 := h6266c.1
                                      have p6266_1 := h6266c.2.1
                                      have p6266_2 := h6266c.2.2.1
                                      have p6266_3 := h6266c.2.2.2
                                      linarith only [hlam, p6266_0]
                              · linarith only [h0, h6137, h6257, h6261, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · linarith only [h0, h6137, h6256, h6260, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · linarith only [h0, h6137, h6144, h6256, h6257, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6299 | h6299
                        · linarith only [h0, h6137, h6143, h6256, h6299, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6301 | h6301
                          · linarith only [h0, h6138, h6145, h6301, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6303 | h6303
                            · linarith only [h6253, h6256, h6303, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6305 | h6305
                              · linarith only [h0, h6137, h6143, h6253, h6256, h6299, h6305, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6307 | h6307
                                · linarith only [h0, h6141, h6143, h6145, h6256, h6307, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6309 | h6309
                                  · linarith only [h6143, h6145, h6309, hlam]
                                  · rcases h1bigk with h6311c | h6311c | h6311c | h6311c | h6311c | h6311c | h6311c | h6311c | h6311c | h6311c | h6311c | h6311c | h6311c | h6311c | h6311c | h6311c | h6311c | h6311c | h6311c | h6311c | h6311c | h6311c | h6311c | h6311c | h6311c
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [hlam, p6311_0]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [h0, hlam, p6311_0]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [h0, h6253, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6311_1]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [h0, h6253, h6256, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6311_1]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [h0, h6253, h6256, h6301, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6311_1]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p6311_1]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [hlam, p6311_0]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      rcases p6311_3 (m.d 0 1) (by simp) with h6319 | h6319
                                      · linarith only [h0, h6319, hlam]
                                      · linarith only [h6137, h6319, hlam]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      rcases p6311_3 (m.d 0 1) (by simp) with h6322 | h6322
                                      · linarith only [h0, h6322, hlam]
                                      · linarith only [h6138, h6322, hlam]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      rcases p6311_3 (m.d 0 1) (by simp) with h6325 | h6325
                                      · linarith only [h0, h6325, hlam]
                                      · linarith only [h6139, h6325, hlam]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [h6137, hlam, p6311_0]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [h6253, hlam, p6311_1]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [hlam, p6311_0]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [h6256, hlam, p6311_1]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [h6299, hlam, p6311_1]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [h6138, hlam, p6311_0]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [h6254, hlam, p6311_1]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [h6138, h6253, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6311_1]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [hlam, p6311_0]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [h6301, hlam, p6311_1]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [h6139, hlam, p6311_0]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [h6255, hlam, p6311_1]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [h0, h6137, h6144, h6253, h6299, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6311_1]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [h0, h6137, h6144, h6299, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p6311_1]
                                    · have p6311_0 := h6311c.1
                                      have p6311_1 := h6311c.2.1
                                      have p6311_2 := h6311c.2.2.1
                                      have p6311_3 := h6311c.2.2.2
                                      linarith only [hlam, p6311_0]
                    · linarith only [h0, h6142, h6255, hlam]
                  · linarith only [h0, h6141, h6254, hlam]
                · linarith only [h0, h6140, h6253, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6346 | h6346
              · linarith only [h6143, h6144, h6346, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6348 | h6348
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6349 | h6349
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6350 | h6350
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6351 | h6351
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6352 | h6352
                        · linarith only [h0, h6137, h6144, h6352, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6354 | h6354
                          · linarith only [h0, h6137, h6138, h6144, h6346, h6351, h6354, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6356 | h6356
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6357 | h6357
                              · linarith only [h6137, h6144, h6348, h6357, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6359 | h6359
                                · linarith only [h6141, h6346, h6359, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6361 | h6361
                                  · linarith only [h6137, h6138, h6144, h6346, h6348, h6349, h6356, h6361, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                                  · rcases h1bigk with h6363c | h6363c | h6363c | h6363c | h6363c | h6363c | h6363c | h6363c | h6363c | h6363c | h6363c | h6363c | h6363c | h6363c | h6363c | h6363c | h6363c | h6363c | h6363c | h6363c | h6363c | h6363c | h6363c | h6363c | h6363c
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [hlam, p6363_0]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [h0, hlam, p6363_0]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [h0, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6363_1]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [h0, h6349, h6356, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6363_1]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6363_1]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p6363_1]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [hlam, p6363_0]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [h6351, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6363_1]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      rcases p6363_3 (m.d 0 1) (by simp) with h6372 | h6372
                                      · linarith only [h0, h6372, hlam]
                                      · linarith only [h6138, h6372, hlam]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [h6348, h6352, h6356, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6363_1]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [h6137, hlam, p6363_0]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [h6348, hlam, p6363_1]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [hlam, p6363_0]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [h6139, h6349, h6352, h6356, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6363_1]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [h6352, hlam, p6363_1]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [h6138, hlam, p6363_0]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [h6349, hlam, p6363_1]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [h6351, hlam, p6363_0]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [hlam, p6363_0]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [h6354, hlam, p6363_1]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [h6139, hlam, p6363_0]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [h6350, hlam, p6363_1]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [h6139, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p6363_1]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [h0, h6139, h6349, h6356, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6363_1]
                                    · have p6363_0 := h6363c.1
                                      have p6363_1 := h6363c.2.1
                                      have p6363_2 := h6363c.2.2.1
                                      have p6363_3 := h6363c.2.2.2
                                      linarith only [hlam, p6363_0]
                            · linarith only [h0, h6137, h6351, h6356, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · linarith only [h6143, h6144, h6351, hc13, hc35, hlam, hphi]
                    · linarith only [h0, h6142, h6350, hlam]
                  · linarith only [h0, h6141, h6349, hlam]
                · linarith only [h0, h6140, h6348, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6396 | h6396
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6397 | h6397
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6398 | h6398
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6399 | h6399
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6400 | h6400
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6401 | h6401
                      · linarith only [h0, h6137, h6143, h6401, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6403 | h6403
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6404 | h6404
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6405 | h6405
                            · linarith only [h0, h6137, h6140, h6143, h6403, h6405, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6407 | h6407
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6408 | h6408
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6409 | h6409
                                  · rcases h1bigk with h6410c | h6410c | h6410c | h6410c | h6410c | h6410c | h6410c | h6410c | h6410c | h6410c | h6410c | h6410c | h6410c | h6410c | h6410c | h6410c | h6410c | h6410c | h6410c | h6410c | h6410c | h6410c | h6410c | h6410c | h6410c
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [hlam, p6410_0]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [h0, hlam, p6410_0]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [h0, h6398, h6407, h6409, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6410_1]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [h0, h6398, h6401, h6407, h6409, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6410_1]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6410_1]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p6410_1]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [hlam, p6410_0]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [h6398, h6407, h6409, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6410_1]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [h6398, h6401, h6407, h6409, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6410_1]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      rcases p6410_3 (m.d 0 1) (by simp) with h6420 | h6420
                                      · linarith only [h0, h6420, hlam]
                                      · linarith only [h6139, h6420, hlam]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [h6137, hlam, p6410_0]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [h6398, hlam, p6410_1]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [hlam, p6410_0]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [h6401, hlam, p6410_1]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [h6138, h6400, h6401, h6407, h6409, hc01, hc45, hlam, hphi, ht0b, ht5b, p6410_1]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [h6138, hlam, p6410_0]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [h6399, hlam, p6410_1]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [h6138, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p6410_1]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [hlam, p6410_0]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [h0, h6138, h6400, h6407, h6409, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6410_1]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [h6139, hlam, p6410_0]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [h6400, hlam, p6410_1]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [h6403, hlam, p6410_0]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [h6404, hlam, p6410_0]
                                    · have p6410_0 := h6410c.1
                                      have p6410_1 := h6410c.2.1
                                      have p6410_2 := h6410c.2.2.1
                                      have p6410_3 := h6410c.2.2.2
                                      linarith only [hlam, p6410_0]
                                  · linarith only [h6137, h6143, h6397, h6398, h6407, h6409, hc04, hc35, hlam, hphi, ht0b, ht5b]
                                · linarith only [h0, h6138, h6404, h6408, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                              · linarith only [h6143, h6396, h6407, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h6138, h6397, h6401, h6403, h6404, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h6143, h6396, h6403, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h6142, h6400, hlam]
                  · linarith only [h0, h6141, h6399, hlam]
                · linarith only [h0, h6140, h6398, hlam]
              · linarith only [h6143, h6396, h6397, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6447 | h6447
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6448 | h6448
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6449 | h6449
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6450 | h6450
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6451 | h6451
                      · linarith only [h6137, h6143, h6451, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6453 | h6453
                        · linarith only [h0, h6137, h6396, h6453, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6455 | h6455
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6456 | h6456
                            · linarith only [h0, h6137, h6138, h6143, h6448, h6455, h6456, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6458 | h6458
                              · linarith only [h6137, h6396, h6448, h6458, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6460 | h6460
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6461 | h6461
                                  · rcases h1bigk with h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [hlam, p6462_0]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [h0, hlam, p6462_0]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [h0, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6462_1]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [h0, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p6462_1]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6462_1]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p6462_1]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [hlam, p6462_0]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      rcases p6462_3 (m.d 0 1) (by simp) with h6470 | h6470
                                      · linarith only [h0, h6470, hlam]
                                      · linarith only [h6137, h6470, hlam]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [h6449, h6460, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6462_1]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      rcases p6462_3 (m.d 0 1) (by simp) with h6474 | h6474
                                      · linarith only [h0, h6474, hlam]
                                      · linarith only [h6139, h6474, hlam]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [h6137, hlam, p6462_0]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [h6448, hlam, p6462_1]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [hlam, p6462_0]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [h6451, hlam, p6462_1]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [h6453, hlam, p6462_1]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [h6138, hlam, p6462_0]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [h6449, hlam, p6462_1]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [h6138, h6448, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6462_1]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [hlam, p6462_0]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [h0, h6138, h6450, h6458, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6462_1]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [h6139, hlam, p6462_0]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [h6450, hlam, p6462_1]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [h0, h6139, h6448, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6462_1]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [h6455, hlam, p6462_0]
                                    · have p6462_0 := h6462c.1
                                      have p6462_1 := h6462c.2.1
                                      have p6462_2 := h6462c.2.2.1
                                      have p6462_3 := h6462c.2.2.2
                                      linarith only [hlam, p6462_0]
                                  · linarith only [h6141, h6143, h6460, h6461, hlam]
                                · linarith only [h0, h6138, h6455, h6460, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6494 | h6494
                            · linarith only [h6143, h6447, h6448, h6451, h6455, h6494, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6496 | h6496
                              · linarith only [h6396, h6447, h6448, h6451, h6455, h6496, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6498 | h6498
                                · linarith only [h6449, h6455, h6498, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6500 | h6500
                                  · rcases h1bigk with h6501c | h6501c | h6501c | h6501c | h6501c | h6501c | h6501c | h6501c | h6501c | h6501c | h6501c | h6501c | h6501c | h6501c | h6501c | h6501c | h6501c | h6501c | h6501c | h6501c | h6501c | h6501c | h6501c | h6501c | h6501c
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [hlam, p6501_0]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [h0, hlam, p6501_0]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [h0, h6448, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6501_1]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [h0, h6448, h6451, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6501_1]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6501_1]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p6501_1]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [hlam, p6501_0]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      rcases p6501_3 (m.d 0 1) (by simp) with h6509 | h6509
                                      · linarith only [h0, h6509, hlam]
                                      · linarith only [h6137, h6509, hlam]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      rcases p6501_3 (m.d 0 1) (by simp) with h6512 | h6512
                                      · linarith only [h0, h6512, hlam]
                                      · linarith only [h6138, h6512, hlam]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      rcases p6501_3 (m.d 0 1) (by simp) with h6515 | h6515
                                      · linarith only [h0, h6515, hlam]
                                      · linarith only [h6139, h6515, hlam]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [h6137, hlam, p6501_0]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [h6448, hlam, p6501_1]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [hlam, p6501_0]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [h6451, hlam, p6501_1]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [h6453, hlam, p6501_1]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [h6138, hlam, p6501_0]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [h6449, hlam, p6501_1]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [h6138, h6447, h6448, h6455, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6501_1]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [hlam, p6501_0]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [h6455, hlam, p6501_1]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [h6139, hlam, p6501_0]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [h6450, hlam, p6501_1]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [h0, h6139, h6448, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6501_1]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [h0, h6138, h6447, h6455, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p6501_1]
                                    · have p6501_0 := h6501c.1
                                      have p6501_1 := h6501c.2.1
                                      have p6501_2 := h6501c.2.2.1
                                      have p6501_3 := h6501c.2.2.2
                                      linarith only [hlam, p6501_0]
                                  · linarith only [h6143, h6447, h6500, hlam]
                    · linarith only [h0, h6142, h6450, hlam]
                  · linarith only [h0, h6141, h6449, hlam]
                · linarith only [h0, h6140, h6448, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6537 | h6537
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6538 | h6538
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6539 | h6539
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6540 | h6540
                      · linarith only [h6137, h6143, h6540, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6542 | h6542
                        · linarith only [h6137, h6396, h6542, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6544 | h6544
                          · linarith only [h0, h6137, h6138, h6143, h6447, h6537, h6544, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6546 | h6546
                            · linarith only [h6137, h6143, h6537, h6546, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6548 | h6548
                              · linarith only [h6137, h6396, h6537, h6548, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6550 | h6550
                                · linarith only [h6141, h6447, h6550, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6552 | h6552
                                  · rcases h1bigk with h6553c | h6553c | h6553c | h6553c | h6553c | h6553c | h6553c | h6553c | h6553c | h6553c | h6553c | h6553c | h6553c | h6553c | h6553c | h6553c | h6553c | h6553c | h6553c | h6553c | h6553c | h6553c | h6553c | h6553c | h6553c
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [hlam, p6553_0]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [h0, hlam, p6553_0]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [h0, h6537, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6553_1]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [h0, h6537, h6540, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6553_1]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [h0, h6537, h6540, h6544, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6553_1]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p6553_1]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [hlam, p6553_0]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      rcases p6553_3 (m.d 0 1) (by simp) with h6561 | h6561
                                      · linarith only [h0, h6561, hlam]
                                      · linarith only [h6137, h6561, hlam]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      rcases p6553_3 (m.d 0 1) (by simp) with h6564 | h6564
                                      · linarith only [h0, h6564, hlam]
                                      · linarith only [h6138, h6564, hlam]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      rcases p6553_3 (m.d 0 1) (by simp) with h6567 | h6567
                                      · linarith only [h0, h6567, hlam]
                                      · linarith only [h6139, h6567, hlam]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [h6137, hlam, p6553_0]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [h6537, hlam, p6553_1]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [hlam, p6553_0]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [h6540, hlam, p6553_1]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [h6542, hlam, p6553_1]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [h6138, hlam, p6553_0]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [h6538, hlam, p6553_1]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [h6139, h6537, h6544, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6553_1]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [hlam, p6553_0]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [h6544, hlam, p6553_1]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [h6139, hlam, p6553_0]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [h6539, hlam, p6553_1]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [h0, h6139, h6537, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6553_1]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [h0, h6139, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p6553_1]
                                    · have p6553_0 := h6553c.1
                                      have p6553_1 := h6553c.2.1
                                      have p6553_2 := h6553c.2.2.1
                                      have p6553_3 := h6553c.2.2.2
                                      linarith only [hlam, p6553_0]
                                  · rcases h1bigk with h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c | h6585c
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [hlam, p6585_0]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [h0, hlam, p6585_0]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [h0, h6537, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6585_1]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [h0, h6538, h6546, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6585_1]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [h0, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p6585_1]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p6585_1]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [hlam, p6585_0]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      rcases p6585_3 (m.d 0 1) (by simp) with h6593 | h6593
                                      · linarith only [h0, h6593, hlam]
                                      · linarith only [h6137, h6593, hlam]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      rcases p6585_3 (m.d 0 1) (by simp) with h6596 | h6596
                                      · linarith only [h0, h6596, hlam]
                                      · linarith only [h6138, h6596, hlam]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      rcases p6585_3 (m.d 0 1) (by simp) with h6599 | h6599
                                      · linarith only [h0, h6599, hlam]
                                      · linarith only [h6139, h6599, hlam]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [h6137, hlam, p6585_0]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [h6537, hlam, p6585_1]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [hlam, p6585_0]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [h6540, hlam, p6585_1]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [h6542, hlam, p6585_1]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [h6138, hlam, p6585_0]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [h6538, hlam, p6585_1]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [h6138, h6537, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6585_1]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [hlam, p6585_0]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [h6544, hlam, p6585_1]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [h6139, hlam, p6585_0]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [h6539, hlam, p6585_1]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [h0, h6139, h6537, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6585_1]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [h0, h6139, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p6585_1]
                                    · have p6585_0 := h6585c.1
                                      have p6585_1 := h6585c.2.1
                                      have p6585_2 := h6585c.2.2.1
                                      have p6585_3 := h6585c.2.2.2
                                      linarith only [hlam, p6585_0]
                    · linarith only [h0, h6142, h6539, hlam]
                  · linarith only [h0, h6141, h6538, hlam]
                · linarith only [h0, h6140, h6537, hlam]
        · linarith only [h0, h6139, h6142, hlam]
      · linarith only [h0, h6138, h6141, hlam]
    · linarith only [h0, h6137, h6140, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6623 | h6623
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6624 | h6624
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6625 | h6625
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6626 | h6626
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6627 | h6627
            · linarith only [h6137, h6139, h6627, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6629 | h6629
              · linarith only [h6137, h6139, h6626, h6629, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6631 | h6631
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6632 | h6632
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6633 | h6633
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6634 | h6634
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6635 | h6635
                        · linarith only [h6137, h6139, h6627, h6633, h6635, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6637 | h6637
                          · linarith only [h6138, h6139, h6629, h6637, hlam]
                          · linarith only [h6137, h6139, h6634, h6637, hc34, hc45, hlam, hphi]
                      · linarith only [h6626, h6627, h6634, hc13, hc35, hlam, hphi]
                    · linarith only [h0, h6138, h6625, h6633, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                  · linarith only [h0, h6624, h6632, hlam]
                · linarith only [h0, h6623, h6631, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6644 | h6644
            · linarith only [h6138, h6139, h6626, h6644, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6646 | h6646
              · linarith only [h6138, h6139, h6646, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6648 | h6648
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6649 | h6649
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6650 | h6650
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6651 | h6651
                      · linarith only [h6137, h6139, h6626, h6651, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6653 | h6653
                        · linarith only [h6137, h6139, h6644, h6653, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6655 | h6655
                          · linarith only [h6138, h6139, h6626, h6646, h6650, h6655, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6657 | h6657
                            · linarith only [h6137, h6139, h6648, h6655, h6657, hc34, hc45, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6659 | h6659
                              · linarith only [h6137, h6644, h6648, h6659, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6661 | h6661
                                · linarith only [h6138, h6139, h6649, h6655, h6661, hlam]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6663 | h6663
                                  · linarith only [h6138, h6139, h6651, h6655, h6663, hc13, hc34, hlam, hphi]
                                  · rcases h1bigk with h6665c | h6665c | h6665c | h6665c | h6665c | h6665c | h6665c | h6665c | h6665c | h6665c | h6665c | h6665c | h6665c | h6665c | h6665c | h6665c | h6665c | h6665c | h6665c | h6665c | h6665c | h6665c | h6665c | h6665c | h6665c
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [hlam, p6665_0]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [h0, hlam, p6665_0]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [h6139, h6648, hc15, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6665_1]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [h6139, hc14, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, p6665_1]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [h6139, hlam, p6665_0]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p6665_1]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [hlam, p6665_0]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      rcases p6665_3 (m.d 0 1) (by simp) with h6673 | h6673
                                      · linarith only [h0, h6673, hlam]
                                      · linarith only [h6137, h6673, hlam]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      rcases p6665_3 (m.d 0 1) (by simp) with h6676 | h6676
                                      · linarith only [h0, h6676, hlam]
                                      · linarith only [h6138, h6676, hlam]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [h6138, h6139, h6648, h6651, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6665_1]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [h6137, hlam, p6665_0]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [h6648, hlam, p6665_1]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [hlam, p6665_0]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [h6651, hlam, p6665_1]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [h6653, hlam, p6665_1]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [h6138, hlam, p6665_0]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [h6649, hlam, p6665_1]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [h6138, h6648, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6665_1]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [hlam, p6665_0]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [h6655, hlam, p6665_1]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [hc01, hc15, hlam, hphi, p6665_1]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [h6650, hlam, p6665_1]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [h6648, h6653, h6663, hc23, hc45, hlam, hphi, ht34, p6665_1]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [h6649, h6653, h6657, h6663, hc23, hc45, hlam, hphi, ht34, p6665_1]
                                    · have p6665_0 := h6665c.1
                                      have p6665_1 := h6665c.2.1
                                      have p6665_2 := h6665c.2.2.1
                                      have p6665_3 := h6665c.2.2.2
                                      linarith only [hlam, p6665_0]
                    · linarith only [h0, h6625, h6650, hlam]
                  · linarith only [h0, h6624, h6649, hlam]
                · linarith only [h0, h6623, h6648, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6698 | h6698
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6699 | h6699
            · linarith only [h0, h6137, h6625, h6699, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6701 | h6701
              · linarith only [h0, h6137, h6625, h6698, h6701, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6703 | h6703
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6704 | h6704
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6705 | h6705
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6706 | h6706
                      · linarith only [h0, h6137, h6625, h6705, h6706, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h0, h6137, h6625, h6698, h6705, h6706, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6709 | h6709
                      · linarith only [h0, h6137, h6705, h6709, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h6137, h6698, h6703, h6705, h6709, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h0, h6137, h6624, h6625, h6698, h6704, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h6623, h6703, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6714 | h6714
            · linarith only [h6137, h6139, h6714, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6716 | h6716
              · linarith only [h0, h6138, h6625, h6716, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6718 | h6718
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6719 | h6719
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6720 | h6720
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6721 | h6721
                      · linarith only [h0, h6137, h6625, h6698, h6720, h6721, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6723 | h6723
                        · linarith only [h0, h6137, h6625, h6714, h6723, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6725 | h6725
                          · linarith only [h0, h6138, h6625, h6716, h6720, h6725, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6727 | h6727
                            · linarith only [h6623, h6625, h6698, h6720, h6727, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6729 | h6729
                              · linarith only [h0, h6137, h6625, h6718, h6720, h6729, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h6731 | h6731
                                · linarith only [h0, h6138, h6625, h6719, h6720, h6725, h6731, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h6733 | h6733
                                  · linarith only [h0, h6138, h6625, h6719, h6720, h6725, h6727, h6733, hc23, hc34, hlam, hphi]
                                  · rcases h1bigk with h6735c | h6735c | h6735c | h6735c | h6735c | h6735c | h6735c | h6735c | h6735c | h6735c | h6735c | h6735c | h6735c | h6735c | h6735c | h6735c | h6735c | h6735c | h6735c | h6735c | h6735c | h6735c | h6735c | h6735c | h6735c
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [hlam, p6735_0]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [h0, hlam, p6735_0]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [h0, h6625, h6720, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6735_1]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [h0, h6625, h6720, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p6735_1]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [h6139, hlam, p6735_0]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [hc01, hc12, hlam, hphi, p6735_1]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [hlam, p6735_0]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      rcases p6735_3 (m.d 0 1) (by simp) with h6743 | h6743
                                      · linarith only [h0, h6743, hlam]
                                      · linarith only [h6137, h6743, hlam]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      rcases p6735_3 (m.d 0 1) (by simp) with h6746 | h6746
                                      · linarith only [h0, h6746, hlam]
                                      · linarith only [h6138, h6746, hlam]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [h6625, h6720, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6735_1]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [h6137, hlam, p6735_0]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [h6718, hlam, p6735_1]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [hlam, p6735_0]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [h6721, hlam, p6735_1]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [h6723, hlam, p6735_1]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [h6138, hlam, p6735_0]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [h6719, hlam, p6735_1]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [h6138, h6718, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6735_1]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [hlam, p6735_0]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [h6725, hlam, p6735_1]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [h6723, h6733, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p6735_1]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [h6720, hlam, p6735_1]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [h6718, h6723, h6733, hc23, hc45, hlam, hphi, ht34, p6735_1]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [h6718, h6721, h6723, h6733, hc23, hc45, hlam, hphi, ht34, p6735_1]
                                    · have p6735_0 := h6735c.1
                                      have p6735_1 := h6735c.2.1
                                      have p6735_2 := h6735c.2.2.1
                                      have p6735_3 := h6735c.2.2.2
                                      linarith only [hlam, p6735_0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6765 | h6765
                      · linarith only [h0, h6137, h6720, h6765, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6767 | h6767
                        · linarith only [h0, h6138, h6720, h6765, h6767, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h6769 | h6769
                          · linarith only [h0, h6138, h6720, h6769, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h6771 | h6771
                            · linarith only [h6137, h6698, h6718, h6771, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h6773 | h6773
                              · linarith only [h0, h6138, h6718, h6720, h6765, h6767, h6773, hc15, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                              · linarith only [h0, h6138, h6718, h6720, h6765, h6773, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h6138, h6624, h6625, h6719, hc05, hc14, hlam, hphi, ht0b, ht45, ht5b]
                · linarith only [h0, h6623, h6718, hlam]
      · linarith only [h0, h6138, h6624, hlam]
    · linarith only [h0, h6137, h6623, hlam]

end R2N4
