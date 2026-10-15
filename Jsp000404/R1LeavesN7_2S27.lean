import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S26

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5036000 in
set_option maxHeartbeats 5036000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s15_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h14397 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0 := hg0
  have h14396 := hg14396
  rcases m.htr 0 1 5 (by decide) (by decide) with h16129 | h16129
  · rcases m.htr 0 2 3 (by decide) (by decide) with h16130 | h16130
    · rcases m.htr 0 2 4 (by decide) (by decide) with h16131 | h16131
      · rcases m.htr 0 2 5 (by decide) (by decide) with h16132 | h16132
        · rcases m.htr 0 3 4 (by decide) (by decide) with h16133 | h16133
          · linarith only [h14396, h14397, h16133, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h16135 | h16135
            · rcases m.htr 0 4 5 (by decide) (by decide) with h16136 | h16136
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16137 | h16137
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16138 | h16138
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16139 | h16139
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16140 | h16140
                      · linarith only [h14396, h14397, h16133, h16138, h16140, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16142 | h16142
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16143 | h16143
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16144 | h16144
                            · linarith only [h14396, h14397, h16137, h16140, h16144, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h16146 | h16146
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h16147 | h16147
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16148 | h16148
                                  · rcases h0bigk with h16149c | h16149c | h16149c | h16149c | h16149c | h16149c | h16149c | h16149c | h16149c | h16149c | h16149c | h16149c | h16149c | h16149c | h16149c | h16149c | h16149c | h16149c | h16149c | h16149c | h16149c | h16149c | h16149c | h16149c | h16149c
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      linarith only [hlam, p16149_0]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      linarith only [h0, hlam, p16149_1]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      linarith only [h14397, h16140, hc03, hc34, hlam, hphi, p16149_1]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      linarith only [h14397, hlam, p16149_1]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      rcases p16149_3 (m.d 0 1) (by simp) with h16154 | h16154
                                      · rcases p16149_3 (m.d 0 2) (by simp) with h16155 | h16155
                                        · rcases p16149_3 (m.d 0 3) (by simp) with h16156 | h16156
                                          · linarith only [h14396, h16156, hlam]
                                          · linarith only [h16135, h16156, hlam]
                                        · linarith only [h16132, h16155, hlam]
                                      · linarith only [h16129, h16154, hlam]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      linarith only [h0, h14396, h16137, h16146, h16148, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16149_1]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      linarith only [hlam, p16149_0]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      rcases p16149_3 (m.d 0 1) (by simp) with h16163 | h16163
                                      · linarith only [h0, h16163, hlam]
                                      · linarith only [h14396, h16163, hlam]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      linarith only [h0, h14396, h14397, h16137, h16146, h16148, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16149_1]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      rcases p16149_3 (m.d 0 1) (by simp) with h16167 | h16167
                                      · linarith only [h0, h16167, hlam]
                                      · linarith only [h16129, h16167, hlam]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      linarith only [h14396, hlam, p16149_1]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      linarith only [h16130, hlam, p16149_1]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      linarith only [hlam, p16149_0]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      linarith only [h16133, hlam, p16149_1]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      rcases p16149_3 (m.d 0 1) (by simp) with h16174 | h16174
                                      · rcases p16149_3 (m.d 0 2) (by simp) with h16175 | h16175
                                        · rcases p16149_3 (m.d 0 3) (by simp) with h16176 | h16176
                                          · rcases p16149_3 (m.d 0 4) (by simp) with h16177 | h16177
                                            · rcases p16149_3 (m.d 0 5) (by simp) with h16178 | h16178
                                              · linarith only [h16135, h16178, hlam]
                                              · rcases h2bigk with h16180c | h16180c | h16180c | h16180c | h16180c | h16180c | h16180c | h16180c | h16180c | h16180c | h16180c | h16180c | h16180c | h16180c | h16180c | h16180c | h16180c | h16180c | h16180c | h16180c | h16180c | h16180c | h16180c | h16180c | h16180c
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  linarith only [hlam, p16180_0]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  linarith only [h0, hlam, p16180_1]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  rcases p16180_3 (m.d 0 2) (by simp) with h16183 | h16183
                                                  · rcases p16180_3 (m.d 1 2) (by simp) with h16184 | h16184
                                                    · rcases p16180_3 (m.d 2 3) (by simp) with h16185 | h16185
                                                      · linarith only [h16185, hlam, p16180_0]
                                                      · rcases p16180_3 (m.d 2 4) (by simp) with h16187 | h16187
                                                        · linarith only [h16131, h16187, hlam]
                                                        · linarith only [h16144, h16187, hlam]
                                                    · linarith only [h16137, h16184, hlam]
                                                  · linarith only [h16183, hlam, p16180_0]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  rcases p16180_3 (m.d 0 2) (by simp) with h16192 | h16192
                                                  · rcases p16180_3 (m.d 1 2) (by simp) with h16193 | h16193
                                                    · rcases p16180_3 (m.d 2 3) (by simp) with h16194 | h16194
                                                      · linarith only [h16130, h16194, hlam]
                                                      · rcases p16180_3 (m.d 2 4) (by simp) with h16196 | h16196
                                                        · linarith only [h16196, hlam, p16180_0]
                                                        · rcases p16180_3 (m.d 2 5) (by simp) with h16198 | h16198
                                                          · linarith only [h16132, h16198, hlam]
                                                          · rcases h3bigk with h16200c | h16200c | h16200c | h16200c | h16200c | h16200c | h16200c | h16200c | h16200c | h16200c | h16200c | h16200c | h16200c | h16200c | h16200c | h16200c | h16200c | h16200c | h16200c | h16200c | h16200c | h16200c | h16200c | h16200c | h16200c
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [hlam, p16200_0]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [h14396, h16137, h16146, h16148, hc01, hc45, hlam, hphi, ht0b, ht5b, p16200_1]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [h14396, h14397, h16140, h16146, h16148, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p16200_1]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [h16133, hlam, p16200_0]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [h14396, h14397, h16140, h16148, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p16200_1]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [h14396, hlam, p16200_0]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [hlam, p16200_0]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [h16146, h16148, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p16200_1]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [h16140, hlam, p16200_0]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [h14396, h14397, h16140, h16148, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p16200_1]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [h16130, hlam, p16200_0]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [h16137, hlam, p16200_0]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [hlam, p16200_0]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [h16144, hlam, p16200_0]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [h16130, h16148, hc02, hc45, hlam, hphi, ht0b, ht5b, p16200_1]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [hc03, hc34, hlam, hphi, p16200_1]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [h16137, hc23, hc34, hlam, hphi, p16200_1]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [hc23, hc34, hlam, hphi, p16200_1]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [hlam, p16200_0]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              rcases p16200_3 (m.d 0 3) (by simp) with h16220 | h16220
                                                              · linarith only [h16133, h16220, hlam]
                                                              · linarith only [h16135, h16220, hlam]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [h16135, hlam, p16200_0]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [h16142, hlam, p16200_0]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [h16146, hlam, p16200_0]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [h16148, hlam, p16200_0]
                                                            · have p16200_0 := h16200c.1
                                                              have p16200_1 := h16200c.2.1
                                                              have p16200_2 := h16200c.2.2.1
                                                              have p16200_3 := h16200c.2.2.2
                                                              linarith only [hlam, p16200_0]
                                                    · linarith only [h16138, h16193, hlam]
                                                  · linarith only [h16192, hlam, p16180_0]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  rcases p16180_3 (m.d 0 2) (by simp) with h16230 | h16230
                                                  · rcases p16180_3 (m.d 1 2) (by simp) with h16231 | h16231
                                                    · rcases p16180_3 (m.d 2 3) (by simp) with h16232 | h16232
                                                      · linarith only [h16130, h16232, hlam]
                                                      · linarith only [h16146, h16232, hlam]
                                                    · linarith only [h16139, h16231, hlam]
                                                  · linarith only [h16230, hlam, p16180_0]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  linarith only [h0, h14396, h16137, h16146, h16148, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16180_1]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  linarith only [hlam, p16180_0]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  rcases p16180_3 (m.d 0 2) (by simp) with h16239 | h16239
                                                  · linarith only [h0, h16239, hlam]
                                                  · linarith only [h16130, h16239, hlam]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  rcases p16180_3 (m.d 0 2) (by simp) with h16242 | h16242
                                                  · linarith only [h0, h16242, hlam]
                                                  · linarith only [h16131, h16242, hlam]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  linarith only [h0, h14396, h16129, h16139, hlam, p16149_1, p16180_2]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  linarith only [h16130, hlam, p16180_0]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  linarith only [h16137, hlam, p16180_0]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  linarith only [hlam, p16180_0]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  linarith only [h16144, hlam, p16180_0]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  linarith only [h14396, h14397, h16137, h16138, h16146, h16148, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16180_1]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  linarith only [h16131, hlam, p16180_0]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  linarith only [h16138, hlam, p16180_0]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  linarith only [h0, h16131, h16146, h16148, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p16180_1]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  linarith only [hlam, p16180_0]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  rcases p16180_3 (m.d 0 2) (by simp) with h16255 | h16255
                                                  · rcases p16180_3 (m.d 1 2) (by simp) with h16256 | h16256
                                                    · rcases p16180_3 (m.d 2 3) (by simp) with h16257 | h16257
                                                      · linarith only [h16144, h16257, hlam]
                                                      · linarith only [h16146, h16257, hlam]
                                                    · linarith only [h16139, h16256, hlam]
                                                  · linarith only [h16132, h16255, hlam]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  linarith only [h16132, hlam, p16180_0]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  linarith only [h16139, hlam, p16180_0]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  linarith only [h16146, hlam, p16180_1]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  linarith only [h16147, hlam, p16180_0]
                                                · have p16180_0 := h16180c.1
                                                  have p16180_1 := h16180c.2.1
                                                  have p16180_2 := h16180c.2.2.1
                                                  have p16180_3 := h16180c.2.2.2
                                                  linarith only [hlam, p16180_0]
                                            · linarith only [h16136, h16177, hlam]
                                          · linarith only [h16135, h16176, hlam]
                                        · linarith only [h16132, h16175, hlam]
                                      · linarith only [h16129, h16174, hlam]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      linarith only [h14396, h14397, h16140, hc13, hc34, hlam, hphi, p16149_1]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      linarith only [h16131, hlam, p16149_0]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      rcases p16149_3 (m.d 0 1) (by simp) with h16273 | h16273
                                      · linarith only [h14397, h16273, hlam]
                                      · linarith only [h14396, h16273, hlam]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      linarith only [hlam, p16149_0]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      rcases p16149_3 (m.d 0 1) (by simp) with h16277 | h16277
                                      · linarith only [h14397, h16277, hlam]
                                      · linarith only [h16129, h16277, hlam]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      linarith only [h16129, hlam, p16149_0]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      linarith only [h16132, hlam, p16149_1]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      linarith only [h16135, hlam, p16149_0]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      linarith only [h16136, hlam, p16149_1]
                                    · have p16149_0 := h16149c.1
                                      have p16149_1 := h16149c.2.1
                                      have p16149_2 := h16149c.2.2.1
                                      have p16149_3 := h16149c.2.2.2
                                      linarith only [hlam, p16149_0]
                                  · linarith only [h14396, h14397, h16140, h16148, hc13, hc45, hlam, hphi, ht34]
                                · linarith only [h14396, h14397, h16142, h16143, h16144, h16146, h16147, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · linarith only [h14396, h14397, h16135, h16140, h16146, hc23, hc34, hlam, hphi]
                          · linarith only [h14396, h14397, h16143, hc13, hc45, hlam, hphi, ht34]
                        · linarith only [h14396, h14397, h16135, h16140, h16142, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h16132, h16139, hlam]
                  · linarith only [h0, h16131, h16138, hlam]
                · linarith only [h0, h16130, h16137, hlam]
              · linarith only [h14397, h16129, h16136, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h16294 | h16294
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16295 | h16295
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16296 | h16296
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16297 | h16297
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16298 | h16298
                      · linarith only [h14396, h14397, h16133, h16296, h16298, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16300 | h16300
                        · linarith only [h14396, h16135, h16300, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16302 | h16302
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16303 | h16303
                            · linarith only [h0, h14397, h16130, h16298, h16303, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h16305 | h16305
                              · linarith only [h14396, h16135, h16295, h16305, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h16307 | h16307
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16308 | h16308
                                  · rcases h0bigk with h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c | h16309c
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      linarith only [hlam, p16309_0]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      linarith only [h0, hlam, p16309_1]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      linarith only [h14397, h16298, hc03, hc34, hlam, hphi, p16309_1]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      linarith only [h14397, hlam, p16309_1]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      linarith only [h14396, h14397, h16135, h16295, h16298, hc23, hc34, hlam, hphi, p16309_1]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      rcases p16309_3 (m.d 0 1) (by simp) with h16315 | h16315
                                      · linarith only [h0, h16315, hlam]
                                      · rcases p16309_3 (m.d 0 2) (by simp) with h16317 | h16317
                                        · rcases p16309_3 (m.d 0 3) (by simp) with h16318 | h16318
                                          · linarith only [h16130, h16318, hlam]
                                          · rcases p16309_3 (m.d 0 4) (by simp) with h16320 | h16320
                                            · linarith only [h16131, h16320, hlam]
                                            · linarith only [h14397, h16320, hlam]
                                        · linarith only [h0, h16317, hlam]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      linarith only [hlam, p16309_0]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      rcases p16309_3 (m.d 0 1) (by simp) with h16325 | h16325
                                      · linarith only [h0, h16325, hlam]
                                      · linarith only [h14396, h16325, hlam]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      rcases p16309_3 (m.d 0 1) (by simp) with h16328 | h16328
                                      · linarith only [h0, h16328, hlam]
                                      · rcases p16309_3 (m.d 0 2) (by simp) with h16330 | h16330
                                        · rcases p16309_3 (m.d 0 3) (by simp) with h16331 | h16331
                                          · linarith only [h16130, h16331, hlam]
                                          · rcases p16309_3 (m.d 0 4) (by simp) with h16333 | h16333
                                            · linarith only [h16131, h16333, hlam]
                                            · rcases p16309_3 (m.d 0 5) (by simp) with h16335 | h16335
                                              · linarith only [h16132, h16335, hlam]
                                              · rcases h2bigk with h16337c | h16337c | h16337c | h16337c | h16337c | h16337c | h16337c | h16337c | h16337c | h16337c | h16337c | h16337c | h16337c | h16337c | h16337c | h16337c | h16337c | h16337c | h16337c | h16337c | h16337c | h16337c | h16337c | h16337c | h16337c
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [hlam, p16337_0]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [h0, hlam, p16337_1]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [h14396, h14397, h16295, hlam, p16309_1, p16337_2]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  rcases p16337_3 (m.d 0 2) (by simp) with h16341 | h16341
                                                  · rcases p16337_3 (m.d 1 2) (by simp) with h16342 | h16342
                                                    · rcases p16337_3 (m.d 2 3) (by simp) with h16343 | h16343
                                                      · linarith only [h16130, h16343, hlam]
                                                      · rcases p16337_3 (m.d 2 4) (by simp) with h16345 | h16345
                                                        · linarith only [h16345, hlam, p16337_0]
                                                        · rcases p16337_3 (m.d 2 5) (by simp) with h16347 | h16347
                                                          · linarith only [h16132, h16347, hlam]
                                                          · rcases h3bigk with h16349c | h16349c | h16349c | h16349c | h16349c | h16349c | h16349c | h16349c | h16349c | h16349c | h16349c | h16349c | h16349c | h16349c | h16349c | h16349c | h16349c | h16349c | h16349c | h16349c | h16349c | h16349c | h16349c | h16349c | h16349c
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [hlam, p16349_0]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [h16135, hc13, hc35, hlam, hphi, p16349_1]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [h0, h14397, h16129, h16135, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16309_1, p16349_1]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [h16133, hlam, p16349_0]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [h16135, hlam, p16349_0]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [h14396, hlam, p16349_0]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [hlam, p16349_0]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [h0, h14397, h16129, h16300, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16309_1, p16349_1]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [h16298, hlam, p16349_0]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [h16300, hlam, p16349_0]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [h16130, hlam, p16349_0]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [h16295, hlam, p16349_0]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [hlam, p16349_0]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [h16303, hlam, p16349_0]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [h16305, hlam, p16349_0]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [hc03, hc34, hlam, hphi, p16349_1]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [hc13, hc34, hlam, hphi, p16349_1]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [hc23, hc34, hlam, hphi, p16349_1]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [hlam, p16349_0]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [h14396, h16135, h16295, hc23, hc34, hlam, hphi, p16349_1]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [h14396, h16295, hc23, hc35, hlam, hphi, p16349_1]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [h16295, hc23, hc35, hlam, hphi, p16349_1]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [hc23, hc35, hlam, hphi, p16349_1]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [h16308, hlam, p16349_0]
                                                            · have p16349_0 := h16349c.1
                                                              have p16349_1 := h16349c.2.1
                                                              have p16349_2 := h16349c.2.2.1
                                                              have p16349_3 := h16349c.2.2.2
                                                              linarith only [hlam, p16349_0]
                                                    · linarith only [h16296, h16342, hlam]
                                                  · linarith only [h16341, hlam, p16337_0]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [h14397, h16129, h16297, hlam, p16309_1, p16337_2]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [h14397, hc01, hc12, hlam, hphi, p16309_1, p16337_1]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [hlam, p16337_0]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [h0, h14396, h14397, h16295, hlam, p16309_1, p16337_2]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  rcases p16337_3 (m.d 0 2) (by simp) with h16381 | h16381
                                                  · linarith only [h0, h16381, hlam]
                                                  · linarith only [h16131, h16381, hlam]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [h0, h14397, h16129, h16297, hlam, p16309_1, p16337_2]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [h16130, hlam, p16337_0]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [h16295, hlam, p16337_0]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [hlam, p16337_0]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [h16303, hlam, p16337_0]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [h16305, hlam, p16337_0]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [h16131, hlam, p16337_0]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [h16296, hlam, p16337_0]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [h16131, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16309_1, p16337_1]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [hlam, p16337_0]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [h0, h16131, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p16309_1, p16337_1]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [h16132, hlam, p16337_0]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [h16297, hlam, p16337_0]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [h0, h14397, h16129, h16132, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16309_1, p16337_1]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [h16307, hlam, p16337_0]
                                                · have p16337_0 := h16337c.1
                                                  have p16337_1 := h16337c.2.1
                                                  have p16337_2 := h16337c.2.2.1
                                                  have p16337_3 := h16337c.2.2.2
                                                  linarith only [hlam, p16337_0]
                                        · linarith only [h16131, h16330, hlam]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      rcases p16309_3 (m.d 0 1) (by simp) with h16401 | h16401
                                      · linarith only [h0, h16401, hlam]
                                      · linarith only [h16129, h16401, hlam]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      linarith only [h14396, hlam, p16309_1]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      linarith only [h16130, hlam, p16309_1]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      linarith only [hlam, p16309_0]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      linarith only [h16133, hlam, p16309_1]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      linarith only [h16135, hlam, p16309_1]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      linarith only [h14396, h16133, h16295, hc23, hc34, hlam, hphi, p16309_1]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      linarith only [h16131, hlam, p16309_0]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      rcases p16309_3 (m.d 0 1) (by simp) with h16411 | h16411
                                      · linarith only [h14397, h16411, hlam]
                                      · linarith only [h14396, h16411, hlam]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      linarith only [hlam, p16309_0]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      rcases p16309_3 (m.d 0 1) (by simp) with h16415 | h16415
                                      · linarith only [h14397, h16415, hlam]
                                      · linarith only [h16129, h16415, hlam]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      linarith only [h16129, hlam, p16309_0]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      linarith only [h16132, hlam, p16309_1]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      linarith only [h14396, h14397, h16129, h16295, h16298, hc23, hc34, hlam, hphi, p16309_1]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      linarith only [h16294, hlam, p16309_1]
                                    · have p16309_0 := h16309c.1
                                      have p16309_1 := h16309c.2.1
                                      have p16309_2 := h16309c.2.2.1
                                      have p16309_3 := h16309c.2.2.2
                                      linarith only [hlam, p16309_0]
                                  · linarith only [h14396, h14397, h16295, h16298, h16308, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h14397, h16129, h16298, h16302, h16303, h16307, hc23, hc34, hlam, hphi]
                          · linarith only [h14397, h16129, h16300, h16302, hc13, hc45, hlam, hphi, ht34]
                    · linarith only [h14396, h14397, h16132, h16295, h16296, h16297, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h14396, h16131, h16295, h16296, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h16130, h16295, hlam]
              · linarith only [h14397, h16129, h16294, hlam]
        · linarith only [h0, h16129, h16132, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h16431 | h16431
        · rcases m.htr 0 3 4 (by decide) (by decide) with h16432 | h16432
          · linarith only [h0, h14396, h16131, h16432, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h16434 | h16434
            · rcases m.htr 0 4 5 (by decide) (by decide) with h16435 | h16435
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16436 | h16436
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16437 | h16437
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16438 | h16438
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16439 | h16439
                      · linarith only [h0, h14396, h16131, h16432, h16437, h16439, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16441 | h16441
                        · linarith only [h0, h14396, h16131, h16437, h16441, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h14396, h16131, h16434, h16436, h16437, h16441, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h16131, h16437, h16438, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16445 | h16445
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16446 | h16446
                      · linarith only [h0, h14396, h16131, h16432, h16437, h16446, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16448 | h16448
                        · linarith only [h0, h14396, h16437, h16448, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h14396, h16434, h16436, h16437, h16448, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h16129, h16131, h16431, h16445, hc04, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h16130, h16436, hlam]
              · linarith only [h0, h14396, h16131, h16434, h16435, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h16454 | h16454
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16455 | h16455
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16456 | h16456
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16457 | h16457
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16458 | h16458
                      · linarith only [h0, h14396, h16131, h16432, h16456, h16458, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16460 | h16460
                        · linarith only [h0, h14396, h16131, h16434, h16456, h16460, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16462 | h16462
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16463 | h16463
                            · linarith only [h14397, h16129, h16130, h16458, h16460, h16463, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h16465 | h16465
                              · linarith only [h0, h16129, h16131, h16434, h16455, h16456, h16460, h16465, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h16467 | h16467
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16468 | h16468
                                  · rcases h0bigk with h16469c | h16469c | h16469c | h16469c | h16469c | h16469c | h16469c | h16469c | h16469c | h16469c | h16469c | h16469c | h16469c | h16469c | h16469c | h16469c | h16469c | h16469c | h16469c | h16469c | h16469c | h16469c | h16469c | h16469c | h16469c
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [hlam, p16469_0]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [h0, hlam, p16469_1]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [h0, h16131, h16456, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16469_1]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [h14397, hlam, p16469_1]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [h0, h16131, h16456, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p16469_1]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [h16131, h16456, hc01, hc12, hlam, hphi, p16469_1]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [hlam, p16469_0]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [h14396, h16131, h16455, h16456, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16469_1]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [h16131, hlam, p16469_1]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [h16129, h16131, h16456, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p16469_1]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [h14396, hlam, p16469_1]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [h16130, hlam, p16469_1]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [hlam, p16469_0]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [h16432, hlam, p16469_1]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [h16434, hlam, p16469_1]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [h14396, h16131, h16455, h16456, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16469_1]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [h0, h14396, h16131, h16455, h16456, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16469_1]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      rcases p16469_3 (m.d 0 1) (by simp) with h16487 | h16487
                                      · linarith only [h14397, h16487, hlam]
                                      · linarith only [h14396, h16487, hlam]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [hlam, p16469_0]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      rcases p16469_3 (m.d 0 1) (by simp) with h16491 | h16491
                                      · linarith only [h14397, h16491, hlam]
                                      · linarith only [h16129, h16491, hlam]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [h16129, hlam, p16469_0]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [h16431, hlam, p16469_1]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [h14396, h14397, h16129, h16455, h16458, hc23, hc34, hlam, hphi, p16469_1]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [h16454, hlam, p16469_1]
                                    · have p16469_0 := h16469c.1
                                      have p16469_1 := h16469c.2.1
                                      have p16469_2 := h16469c.2.2.1
                                      have p16469_3 := h16469c.2.2.2
                                      linarith only [hlam, p16469_0]
                                  · linarith only [h14396, h14397, h16455, h16458, h16468, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h0, h16129, h16131, h16462, h16467, hlam]
                          · linarith only [h0, h16129, h16131, h16455, h16456, h16460, h16462, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h16131, h16431, h16457, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16503 | h16503
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16504 | h16504
                      · linarith only [h0, h14396, h16432, h16456, h16504, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16506 | h16506
                        · linarith only [h14396, h16434, h16506, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16508 | h16508
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16509 | h16509
                            · linarith only [h0, h16129, h16455, h16456, h16504, h16506, h16509, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h0, h16129, h16455, h16456, h16506, h16509, hc23, hc34, hlam, hphi]
                          · linarith only [h0, h16129, h16455, h16456, h16506, h16508, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h16129, h16131, h16431, h16503, hc04, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h16130, h16455, hlam]
              · linarith only [h0, h16129, h16131, h16454, hlam]
        · linarith only [h0, h16129, h16431, hlam]
    · linarith only [h0, h14396, h16130, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h16518 | h16518
    · rcases m.htr 0 2 4 (by decide) (by decide) with h16519 | h16519
      · rcases m.htr 0 2 5 (by decide) (by decide) with h16520 | h16520
        · rcases m.htr 0 3 4 (by decide) (by decide) with h16521 | h16521
          · linarith only [h14396, h14397, h16521, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h16523 | h16523
            · linarith only [h14396, h16129, h16523, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h16525 | h16525
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16526 | h16526
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16527 | h16527
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16528 | h16528
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16529 | h16529
                      · linarith only [h14396, h16129, h16521, h16529, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16531 | h16531
                        · linarith only [h14396, h16129, h16523, h16531, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16533 | h16533
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16534 | h16534
                            · linarith only [h14396, h16129, h16518, h16529, h16533, h16534, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h16536 | h16536
                              · linarith only [h14396, h16129, h16526, h16531, h16536, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h16538 | h16538
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16539 | h16539
                                  · rcases h0bigk with h16540c | h16540c | h16540c | h16540c | h16540c | h16540c | h16540c | h16540c | h16540c | h16540c | h16540c | h16540c | h16540c | h16540c | h16540c | h16540c | h16540c | h16540c | h16540c | h16540c | h16540c | h16540c | h16540c | h16540c | h16540c
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      linarith only [hlam, p16540_0]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      linarith only [h0, hlam, p16540_1]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      linarith only [h14396, h16129, h16526, h16529, h16533, hc23, hc34, hlam, hphi, p16540_1]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      linarith only [h14397, hlam, p16540_1]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      linarith only [h16129, hlam, p16540_1]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      rcases p16540_3 (m.d 0 1) (by simp) with h16546 | h16546
                                      · linarith only [h0, h16546, hlam]
                                      · rcases p16540_3 (m.d 0 2) (by simp) with h16548 | h16548
                                        · rcases p16540_3 (m.d 0 3) (by simp) with h16549 | h16549
                                          · linarith only [h16518, h16549, hlam]
                                          · rcases p16540_3 (m.d 0 4) (by simp) with h16551 | h16551
                                            · linarith only [h16519, h16551, hlam]
                                            · linarith only [h14397, h16551, hlam]
                                        · linarith only [h0, h16548, hlam]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      linarith only [hlam, p16540_0]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      rcases p16540_3 (m.d 0 1) (by simp) with h16556 | h16556
                                      · linarith only [h0, h16556, hlam]
                                      · linarith only [h14396, h16556, hlam]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      rcases p16540_3 (m.d 0 1) (by simp) with h16559 | h16559
                                      · linarith only [h0, h16559, hlam]
                                      · rcases p16540_3 (m.d 0 2) (by simp) with h16561 | h16561
                                        · rcases p16540_3 (m.d 0 3) (by simp) with h16562 | h16562
                                          · linarith only [h16518, h16562, hlam]
                                          · rcases p16540_3 (m.d 0 4) (by simp) with h16564 | h16564
                                            · linarith only [h16519, h16564, hlam]
                                            · rcases p16540_3 (m.d 0 5) (by simp) with h16566 | h16566
                                              · linarith only [h16520, h16566, hlam]
                                              · rcases h2bigk with h16568c | h16568c | h16568c | h16568c | h16568c | h16568c | h16568c | h16568c | h16568c | h16568c | h16568c | h16568c | h16568c | h16568c | h16568c | h16568c | h16568c | h16568c | h16568c | h16568c | h16568c | h16568c | h16568c | h16568c | h16568c
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [hlam, p16568_0]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [h0, hlam, p16568_1]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [h14396, h16129, h16525, h16526, hlam, p16540_1, p16568_2]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  rcases p16568_3 (m.d 0 2) (by simp) with h16572 | h16572
                                                  · rcases p16568_3 (m.d 1 2) (by simp) with h16573 | h16573
                                                    · rcases p16568_3 (m.d 2 3) (by simp) with h16574 | h16574
                                                      · linarith only [h16518, h16574, hlam]
                                                      · rcases p16568_3 (m.d 2 4) (by simp) with h16576 | h16576
                                                        · linarith only [h16576, hlam, p16568_0]
                                                        · rcases p16568_3 (m.d 2 5) (by simp) with h16578 | h16578
                                                          · linarith only [h16520, h16578, hlam]
                                                          · rcases h3bigk with h16580c | h16580c | h16580c | h16580c | h16580c | h16580c | h16580c | h16580c | h16580c | h16580c | h16580c | h16580c | h16580c | h16580c | h16580c | h16580c | h16580c | h16580c | h16580c | h16580c | h16580c | h16580c | h16580c | h16580c | h16580c
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [hlam, p16580_0]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [h0, h14396, h16129, h16525, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16540_1, p16580_1]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [h0, h14396, h16129, h16525, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16540_1, p16580_1]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [h16521, hlam, p16580_0]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [h16523, hlam, p16580_0]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [h14396, hlam, p16580_0]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [hlam, p16580_0]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [h0, h14396, h16129, h16525, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16540_1, p16580_1]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [h16529, hlam, p16580_0]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [h16531, hlam, p16580_0]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [h16518, hlam, p16580_0]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [h16526, hlam, p16580_0]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [hlam, p16580_0]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [h16534, hlam, p16580_0]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [h16536, hlam, p16580_0]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [hc03, hc34, hlam, hphi, p16580_1]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [h16526, hc23, hc34, hlam, hphi, p16580_1]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [hc23, hc34, hlam, hphi, p16580_1]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [hlam, p16580_0]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [h16129, h16531, hc01, hc34, hlam, hphi, ht12, ht23, p16580_1]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [h14396, h16526, hc23, hc35, hlam, hphi, p16580_1]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [h16526, hc23, hc35, hlam, hphi, p16580_1]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [hc23, hc35, hlam, hphi, p16580_1]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [h16539, hlam, p16580_0]
                                                            · have p16580_0 := h16580c.1
                                                              have p16580_1 := h16580c.2.1
                                                              have p16580_2 := h16580c.2.2.1
                                                              have p16580_3 := h16580c.2.2.2
                                                              linarith only [hlam, p16580_0]
                                                    · linarith only [h16527, h16573, hlam]
                                                  · linarith only [h16572, hlam, p16568_0]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  rcases p16568_3 (m.d 0 2) (by simp) with h16608 | h16608
                                                  · rcases p16568_3 (m.d 1 2) (by simp) with h16609 | h16609
                                                    · rcases p16568_3 (m.d 2 3) (by simp) with h16610 | h16610
                                                      · linarith only [h16518, h16610, hlam]
                                                      · rcases p16568_3 (m.d 2 4) (by simp) with h16612 | h16612
                                                        · linarith only [h16519, h16612, hlam]
                                                        · linarith only [h16538, h16612, hlam]
                                                    · linarith only [h16528, h16609, hlam]
                                                  · linarith only [h16608, hlam, p16568_0]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [h14396, h16129, h16525, h16526, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16540_1, p16568_1]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [hlam, p16568_0]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [h0, h14396, h16129, h16525, h16526, hlam, p16540_1, p16568_2]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  rcases p16568_3 (m.d 0 2) (by simp) with h16620 | h16620
                                                  · linarith only [h0, h16620, hlam]
                                                  · linarith only [h16519, h16620, hlam]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  rcases p16568_3 (m.d 0 2) (by simp) with h16623 | h16623
                                                  · linarith only [h0, h16623, hlam]
                                                  · linarith only [h16520, h16623, hlam]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [h16518, hlam, p16568_0]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [h16526, hlam, p16568_0]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [hlam, p16568_0]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [h16534, hlam, p16568_0]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [h16536, hlam, p16568_0]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [h16519, hlam, p16568_0]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [h16527, hlam, p16568_0]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [h16519, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p16540_1, p16568_1]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [hlam, p16568_0]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [h0, h16519, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p16540_1, p16568_1]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [h16520, hlam, p16568_0]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [h16528, hlam, p16568_0]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [h0, h16520, h16525, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16540_1, p16568_1]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [h16538, hlam, p16568_0]
                                                · have p16568_0 := h16568c.1
                                                  have p16568_1 := h16568c.2.1
                                                  have p16568_2 := h16568c.2.2.1
                                                  have p16568_3 := h16568c.2.2.2
                                                  linarith only [hlam, p16568_0]
                                        · linarith only [h16519, h16561, hlam]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      rcases p16540_3 (m.d 0 1) (by simp) with h16642 | h16642
                                      · linarith only [h0, h16642, hlam]
                                      · rcases p16540_3 (m.d 0 2) (by simp) with h16644 | h16644
                                        · rcases p16540_3 (m.d 0 3) (by simp) with h16645 | h16645
                                          · linarith only [h16518, h16645, hlam]
                                          · rcases p16540_3 (m.d 0 4) (by simp) with h16647 | h16647
                                            · linarith only [h16519, h16647, hlam]
                                            · linarith only [h16525, h16647, hlam]
                                        · linarith only [h16520, h16644, hlam]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      linarith only [h14396, hlam, p16540_1]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      linarith only [h16518, hlam, p16540_1]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      linarith only [hlam, p16540_0]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      linarith only [h16521, hlam, p16540_1]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      linarith only [h16523, hlam, p16540_1]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      linarith only [h14396, h14397, h16526, h16529, hc23, hc34, hlam, hphi, p16540_1]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      linarith only [h16519, hlam, p16540_0]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      rcases p16540_3 (m.d 0 1) (by simp) with h16658 | h16658
                                      · linarith only [h14397, h16658, hlam]
                                      · linarith only [h14396, h16658, hlam]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      linarith only [hlam, p16540_0]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      linarith only [h14396, h14397, h16129, h16526, h16529, hc23, hc34, hlam, hphi, p16540_1]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      linarith only [h14396, h16523, h16526, h16539, hc23, hc34, hlam, hphi, p16540_1]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      linarith only [h16520, hlam, p16540_1]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      rcases p16540_3 (m.d 0 1) (by simp) with h16665 | h16665
                                      · linarith only [h16129, h16665, hlam]
                                      · linarith only [h14396, h16665, hlam]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      linarith only [h16525, hlam, p16540_1]
                                    · have p16540_0 := h16540c.1
                                      have p16540_1 := h16540c.2.1
                                      have p16540_2 := h16540c.2.2.1
                                      have p16540_3 := h16540c.2.2.2
                                      linarith only [hlam, p16540_0]
                                  · linarith only [h0, h14396, h14397, h16519, h16526, h16529, h16538, h16539, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16671 | h16671
                                  · rcases h0bigk with h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c | h16672c
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [hlam, p16672_0]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [h0, hlam, p16672_1]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [h14396, h16129, h16526, h16529, h16533, hc23, hc34, hlam, hphi, p16672_1]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [h14397, hlam, p16672_1]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [h16129, hlam, p16672_1]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      rcases p16672_3 (m.d 0 1) (by simp) with h16678 | h16678
                                      · linarith only [h0, h16678, hlam]
                                      · rcases p16672_3 (m.d 0 2) (by simp) with h16680 | h16680
                                        · rcases p16672_3 (m.d 0 3) (by simp) with h16681 | h16681
                                          · linarith only [h16518, h16681, hlam]
                                          · rcases p16672_3 (m.d 0 4) (by simp) with h16683 | h16683
                                            · linarith only [h16519, h16683, hlam]
                                            · linarith only [h14397, h16683, hlam]
                                        · linarith only [h0, h16680, hlam]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [hlam, p16672_0]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      rcases p16672_3 (m.d 0 1) (by simp) with h16688 | h16688
                                      · linarith only [h0, h16688, hlam]
                                      · linarith only [h14396, h16688, hlam]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [h0, h16525, h16534, h16538, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16672_1]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      rcases p16672_3 (m.d 0 1) (by simp) with h16692 | h16692
                                      · linarith only [h0, h16692, hlam]
                                      · rcases p16672_3 (m.d 0 2) (by simp) with h16694 | h16694
                                        · rcases p16672_3 (m.d 0 3) (by simp) with h16695 | h16695
                                          · linarith only [h16518, h16695, hlam]
                                          · rcases p16672_3 (m.d 0 4) (by simp) with h16697 | h16697
                                            · linarith only [h16519, h16697, hlam]
                                            · linarith only [h16525, h16697, hlam]
                                        · linarith only [h16520, h16694, hlam]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [h14396, hlam, p16672_1]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [h16518, hlam, p16672_1]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [hlam, p16672_0]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [h16521, hlam, p16672_1]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [h16523, hlam, p16672_1]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [h14396, h14397, h16526, h16529, hc23, hc34, hlam, hphi, p16672_1]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [h16519, hlam, p16672_0]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      rcases p16672_3 (m.d 0 1) (by simp) with h16708 | h16708
                                      · linarith only [h14397, h16708, hlam]
                                      · linarith only [h14396, h16708, hlam]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [hlam, p16672_0]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [h14396, h14397, h16129, h16526, h16529, hc23, hc34, hlam, hphi, p16672_1]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [h14396, h16129, h16526, h16529, h16533, hc23, hc34, hlam, hphi, p16672_1]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [h16520, hlam, p16672_1]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      rcases p16672_3 (m.d 0 1) (by simp) with h16715 | h16715
                                      · linarith only [h16129, h16715, hlam]
                                      · linarith only [h14396, h16715, hlam]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [h16525, hlam, p16672_1]
                                    · have p16672_0 := h16672c.1
                                      have p16672_1 := h16672c.2.1
                                      have p16672_2 := h16672c.2.2.1
                                      have p16672_3 := h16672c.2.2.2
                                      linarith only [hlam, p16672_0]
                                  · linarith only [h14396, h14397, h16526, h16529, h16671, hc23, hc45, hlam, hphi, ht34]
                          · linarith only [h14397, h16525, h16533, hlam]
                    · linarith only [h0, h16520, h16528, hlam]
                  · linarith only [h0, h16519, h16527, hlam]
                · linarith only [h0, h16518, h16526, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16725 | h16725
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16726 | h16726
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16727 | h16727
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16728 | h16728
                      · linarith only [h14396, h14397, h16525, h16728, hc34, hc45, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16730 | h16730
                        · linarith only [h14396, h16523, h16730, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16732 | h16732
                          · linarith only [h14396, h14397, h16525, h16725, h16728, h16732, hc23, hc34, hlam, hphi]
                          · linarith only [h14396, h14397, h16725, h16732, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h16520, h16727, hlam]
                  · linarith only [h0, h14396, h16519, h16725, h16726, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h16518, h16725, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h16738 | h16738
          · linarith only [h14396, h14397, h16738, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h16740 | h16740
            · linarith only [h0, h14396, h16520, h16740, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h16742 | h16742
              · linarith only [h16519, h16520, h16742, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16744 | h16744
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16745 | h16745
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16746 | h16746
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16747 | h16747
                      · linarith only [h14396, h14397, h16519, h16520, h16738, h16746, h16747, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16749 | h16749
                        · linarith only [h14396, h14397, h16519, h16520, h16740, h16749, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16751 | h16751
                          · linarith only [h14396, h14397, h16742, h16744, h16747, h16751, hc23, hc34, hlam, hphi]
                          · linarith only [h14396, h14397, h16744, h16751, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16754 | h16754
                      · linarith only [h0, h14396, h16746, h16754, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16756 | h16756
                        · linarith only [h14396, h14397, h16745, h16746, h16756, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16758 | h16758
                          · linarith only [h14396, h14397, h16742, h16744, h16745, h16746, h16758, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · linarith only [h14396, h14397, h16744, h16758, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h14396, h16519, h16744, h16745, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h16518, h16744, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h16763 | h16763
        · rcases m.htr 0 3 4 (by decide) (by decide) with h16764 | h16764
          · linarith only [h0, h14396, h16519, h16764, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h16766 | h16766
            · linarith only [h14396, h16129, h16766, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h16768 | h16768
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16769 | h16769
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16770 | h16770
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16771 | h16771
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16772 | h16772
                      · linarith only [h14396, h16129, h16519, h16763, h16764, h16770, h16772, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16774 | h16774
                        · linarith only [h14396, h16129, h16766, h16774, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16776 | h16776
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16777 | h16777
                            · linarith only [h14396, h16129, h16519, h16763, h16769, h16770, h16772, h16777, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h16779 | h16779
                              · linarith only [h14396, h16129, h16519, h16763, h16769, h16770, h16779, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h16781 | h16781
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16782 | h16782
                                  · rcases h0bigk with h16783c | h16783c | h16783c | h16783c | h16783c | h16783c | h16783c | h16783c | h16783c | h16783c | h16783c | h16783c | h16783c | h16783c | h16783c | h16783c | h16783c | h16783c | h16783c | h16783c | h16783c | h16783c | h16783c | h16783c | h16783c
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [hlam, p16783_0]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [h0, hlam, p16783_1]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [h14396, h16129, h16519, h16763, h16769, h16770, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16783_1]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [h14397, hlam, p16783_1]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [h16129, hlam, p16783_1]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [h16519, h16770, hc01, hc12, hlam, hphi, p16783_1]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [hlam, p16783_0]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [h14396, h16519, h16769, h16770, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16783_1]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [h16519, hlam, p16783_1]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [h16519, h16770, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p16783_1]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [h14396, hlam, p16783_1]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [h16518, hlam, p16783_1]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [hlam, p16783_0]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [h16764, hlam, p16783_1]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [h16766, hlam, p16783_1]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [h14396, h14397, h16769, h16772, hc23, hc34, hlam, hphi, p16783_1]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [h16519, h16763, h16770, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b, p16783_1]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      rcases p16783_3 (m.d 0 1) (by simp) with h16801 | h16801
                                      · linarith only [h14397, h16801, hlam]
                                      · linarith only [h14396, h16801, hlam]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [hlam, p16783_0]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [h14396, h16129, h16519, h16769, h16770, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16783_1]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [h14396, h16129, h16769, h16772, h16776, hc23, hc34, hlam, hphi, p16783_1]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [h16763, hlam, p16783_1]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [h14396, h16519, h16763, h16769, h16770, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16783_1]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [h16768, hlam, p16783_1]
                                    · have p16783_0 := h16783c.1
                                      have p16783_1 := h16783c.2.1
                                      have p16783_2 := h16783c.2.2.1
                                      have p16783_3 := h16783c.2.2.2
                                      linarith only [hlam, p16783_0]
                                  · linarith only [h14396, h14397, h16769, h16772, h16782, hc23, hc45, hlam, hphi, ht34]
                                · linarith only [h16519, h16763, h16768, h16781, hlam]
                          · linarith only [h16519, h16763, h16768, h16770, h16776, hlam]
                    · linarith only [h16519, h16763, h16771, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16815 | h16815
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16816 | h16816
                      · linarith only [h14396, h16129, h16764, h16770, h16815, h16816, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16818 | h16818
                        · linarith only [h14396, h16129, h16770, h16815, h16818, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16820 | h16820
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16821 | h16821
                            · linarith only [h14396, h16129, h16769, h16770, h16815, h16816, h16821, hc14, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                            · linarith only [h14396, h16129, h16770, h16815, h16821, hc13, hc34, hlam, hphi]
                          · linarith only [h14396, h16129, h16768, h16769, h16770, h16815, h16820, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h14396, h16763, h16769, h16815, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h16518, h16769, hlam]
              · linarith only [h16519, h16763, h16768, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h16828 | h16828
          · linarith only [h0, h14396, h16519, h16828, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h16830 | h16830
            · linarith only [h14396, h16129, h16830, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h16832 | h16832
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16833 | h16833
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16834 | h16834
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16835 | h16835
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16836 | h16836
                      · linarith only [h0, h14396, h16519, h16828, h16834, h16836, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16838 | h16838
                        · linarith only [h0, h14396, h16763, h16830, h16838, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16840 | h16840
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16841 | h16841
                            · linarith only [h14397, h16518, h16519, h16834, h16836, h16841, hc01, hc12, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h16843 | h16843
                              · linarith only [h0, h14396, h16763, h16833, h16835, h16838, h16843, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h16845 | h16845
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h16846 | h16846
                                  · rcases h0bigk with h16847c | h16847c | h16847c | h16847c | h16847c | h16847c | h16847c | h16847c | h16847c | h16847c | h16847c | h16847c | h16847c | h16847c | h16847c | h16847c | h16847c | h16847c | h16847c | h16847c | h16847c | h16847c | h16847c | h16847c | h16847c
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [hlam, p16847_0]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [h0, hlam, p16847_1]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [h0, h14396, h16763, h16833, h16835, h16836, h16840, hc23, hc34, hlam, hphi, p16847_1]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [h14397, hlam, p16847_1]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [h16129, hlam, p16847_1]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [h16763, h16835, h16840, hc01, hc14, hlam, hphi, p16847_1]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [hlam, p16847_0]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [h14396, h16763, h16833, h16835, h16836, h16840, hc23, hc34, hlam, hphi, p16847_1]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [h16519, hlam, p16847_1]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [h16763, hlam, p16847_0]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [h14396, hlam, p16847_1]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [h16518, hlam, p16847_1]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [hlam, p16847_0]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [h16828, hlam, p16847_1]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [h16830, hlam, p16847_1]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [h14396, h14397, h16833, h16836, hc23, hc34, hlam, hphi, p16847_1]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [h0, h14396, h16519, h16833, h16834, h16836, hc23, hc34, hlam, hphi, p16847_1]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      rcases p16847_3 (m.d 0 1) (by simp) with h16865 | h16865
                                      · linarith only [h14397, h16865, hlam]
                                      · linarith only [h14396, h16865, hlam]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [hlam, p16847_0]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [h0, h14396, h16519, h16763, h16833, h16834, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16847_1]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [h14396, h16129, h16833, h16836, h16840, hc23, hc34, hlam, hphi, p16847_1]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [h0, h14396, h16763, h16833, h16834, h16845, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p16847_1]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      rcases p16847_3 (m.d 0 1) (by simp) with h16872 | h16872
                                      · linarith only [h16129, h16872, hlam]
                                      · linarith only [h14396, h16872, hlam]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [h16832, hlam, p16847_1]
                                    · have p16847_0 := h16847c.1
                                      have p16847_1 := h16847c.2.1
                                      have p16847_2 := h16847c.2.2.1
                                      have p16847_3 := h16847c.2.2.2
                                      linarith only [hlam, p16847_0]
                                  · linarith only [h14396, h14397, h16519, h16832, h16833, h16834, h16836, h16846, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                · linarith only [h16519, h16832, h16845, hlam]
                          · linarith only [h14396, h14397, h16832, h16833, h16840, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h14396, h16519, h16833, h16834, h16835, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16881 | h16881
                    · linarith only [h0, h14396, h16763, h16833, h16834, h16881, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16883 | h16883
                      · linarith only [h0, h14396, h16828, h16834, h16883, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16885 | h16885
                        · linarith only [h0, h14396, h16763, h16830, h16885, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16887 | h16887
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h16888 | h16888
                            · linarith only [h0, h14396, h16833, h16881, h16883, h16887, h16888, hlam]
                            · linarith only [h0, h14396, h16833, h16834, h16888, hc23, hc34, hlam, hphi]
                          · linarith only [h14396, h14397, h16833, h16887, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h14396, h16518, h16763, h16832, h16833, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h16893 | h16893
                · rcases m.htr 1 2 4 (by decide) (by decide) with h16894 | h16894
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16895 | h16895
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16896 | h16896
                      · linarith only [h0, h14396, h16519, h16894, h16896, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16898 | h16898
                        · linarith only [h0, h14396, h16519, h16894, h16898, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16900 | h16900
                          · linarith only [h14396, h14397, h16832, h16896, h16900, hc13, hc34, hlam, hphi]
                          · linarith only [h14396, h14397, h16893, h16900, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h16519, h16894, h16895, hc02, hc25, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h16904 | h16904
                    · linarith only [h0, h14396, h16763, h16893, h16894, h16904, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h16906 | h16906
                      · linarith only [h0, h14396, h16894, h16906, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h16908 | h16908
                        · linarith only [h0, h14396, h16894, h16908, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h16910 | h16910
                          · linarith only [h14396, h14397, h16832, h16893, h16906, h16910, hc23, hc34, hlam, hphi]
                          · linarith only [h14396, h14397, h16893, h16910, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h14396, h16518, h16893, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · linarith only [h0, h14396, h16518, hlam]

set_option maxHeartbeats 5036000 in
set_option maxHeartbeats 5036000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s15 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14396 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0 := hg0
  have h14396 := hg14396
  rcases m.htr 0 1 4 (by decide) (by decide) with h14397 | h14397
  · exact r1l7_10_12_23_L_I_L_I_H_I_s15_x0 m hb0 hb2 hb3 hg0 hg14396 h14397
  · exact r1l7_10_12_23_L_I_L_I_H_I_s15_x1 m hb0 hb2 hb3 hg0 hg14396 h14397

end R2N4
