import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_2S15

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7336000 in
set_option maxHeartbeats 7336000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s12_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h9250 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
    (h11850 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  rcases m.htr 0 4 5 (by decide) (by decide) with h12164 | h12164
  · rcases m.htr 1 2 3 (by decide) (by decide) with h12165 | h12165
    · linarith only [h0, h12165, h4, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h12167 | h12167
      · linarith only [h0, h12167, h7337, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h12169 | h12169
        · linarith only [h0, h12169, h8360, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h12171 | h12171
          · linarith only [h1, h12171, h9250, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h12173 | h12173
            · linarith only [h1, h11850, h12173, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h12175 | h12175
              · rcases m.htr 2 3 4 (by decide) (by decide) with h12176 | h12176
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12177 | h12177
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12178 | h12178
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12179 | h12179
                      · rcases h0bigk with h12180c | h12180c | h12180c | h12180c | h12180c | h12180c | h12180c | h12180c | h12180c | h12180c | h12180c | h12180c | h12180c | h12180c | h12180c | h12180c | h12180c | h12180c | h12180c | h12180c | h12180c | h12180c | h12180c | h12180c | h12180c
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [hlam, p12180_0]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          rcases p12180_3 (m.d 0 1) (by simp) with h12182 | h12182
                          · rcases p12180_3 (m.d 0 2) (by simp) with h12183 | h12183
                            · linarith only [h0, h12183, hlam]
                            · rcases p12180_3 (m.d 0 3) (by simp) with h12185 | h12185
                              · linarith only [h1, h12185, hlam]
                              · linarith only [h12185, h4, hlam]
                          · linarith only [h0, h12182, hlam]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          rcases p12180_3 (m.d 0 1) (by simp) with h12189 | h12189
                          · rcases p12180_3 (m.d 0 2) (by simp) with h12190 | h12190
                            · linarith only [h0, h12190, hlam]
                            · rcases p12180_3 (m.d 0 3) (by simp) with h12192 | h12192
                              · linarith only [h1, h12192, hlam]
                              · rcases p12180_3 (m.d 0 4) (by simp) with h12194 | h12194
                                · linarith only [h12194, h2, hlam]
                                · linarith only [h12194, h9250, hlam]
                          · linarith only [h1, h12189, hlam]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          rcases p12180_3 (m.d 0 1) (by simp) with h12198 | h12198
                          · rcases p12180_3 (m.d 0 2) (by simp) with h12199 | h12199
                            · linarith only [h0, h12199, hlam]
                            · rcases p12180_3 (m.d 0 3) (by simp) with h12201 | h12201
                              · linarith only [h1, h12201, hlam]
                              · rcases p12180_3 (m.d 0 4) (by simp) with h12203 | h12203
                                · linarith only [h12203, h2, hlam]
                                · rcases p12180_3 (m.d 0 5) (by simp) with h12205 | h12205
                                  · linarith only [h12205, h3, hlam]
                                  · rcases h2bigk with h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c | h12207c
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      linarith only [hlam, p12207_0]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      linarith only [h11850, h12177, h12178, h4, hc12, hc24, hlam, hphi, p12207_1]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      linarith only [h4, hlam, p12207_0]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      linarith only [h7337, hlam, p12207_0]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      linarith only [h8360, hlam, p12207_0]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      linarith only [h0, hlam, p12207_0]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      linarith only [hlam, p12207_0]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      linarith only [h12165, hlam, p12207_0]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      linarith only [h12167, hlam, p12207_0]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      linarith only [h12169, hlam, p12207_0]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      rcases p12207_3 (m.d 0 2) (by simp) with h12218 | h12218
                                      · linarith only [h12218, hlam, p12207_0]
                                      · rcases p12207_3 (m.d 1 2) (by simp) with h12220 | h12220
                                        · linarith only [h12165, h12220, hlam]
                                        · rcases p12207_3 (m.d 2 3) (by simp) with h12222 | h12222
                                          · rcases p12207_3 (m.d 2 4) (by simp) with h12223 | h12223
                                            · linarith only [h12176, h12223, hlam]
                                            · linarith only [h12223, h7337, hlam]
                                          · linarith only [h12222, hlam, p12207_0]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      rcases p12207_3 (m.d 0 2) (by simp) with h12227 | h12227
                                      · linarith only [h12227, h4, hlam]
                                      · linarith only [h0, h12227, hlam]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      linarith only [hlam, p12207_0]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      linarith only [h7337, hc02, hc23, hlam, hphi, p12207_1]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      linarith only [h0, h8360, hc12, hc23, hlam, hphi, p12207_1]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      rcases p12207_3 (m.d 0 2) (by simp) with h12233 | h12233
                                      · linarith only [h12233, hlam, p12207_0]
                                      · rcases p12207_3 (m.d 1 2) (by simp) with h12235 | h12235
                                        · linarith only [h12167, h12235, hlam]
                                        · rcases p12207_3 (m.d 2 3) (by simp) with h12237 | h12237
                                          · rcases p12207_3 (m.d 2 4) (by simp) with h12238 | h12238
                                            · rcases p12207_3 (m.d 2 5) (by simp) with h12239 | h12239
                                              · linarith only [h12178, h12239, hlam]
                                              · linarith only [h12239, h8360, hlam]
                                            · linarith only [h12238, hlam, p12207_0]
                                          · linarith only [h12237, h4, hlam]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      rcases p12207_3 (m.d 0 2) (by simp) with h12244 | h12244
                                      · linarith only [h12244, h7337, hlam]
                                      · linarith only [h0, h12244, hlam]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      linarith only [h12176, hlam, p12207_1]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      linarith only [hlam, p12207_0]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      linarith only [h0, h11850, h12177, h4, hc12, hc24, hlam, hphi, p12207_1]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      rcases p12207_3 (m.d 0 2) (by simp) with h12250 | h12250
                                      · linarith only [h12250, hlam, p12207_0]
                                      · rcases p12207_3 (m.d 1 2) (by simp) with h12252 | h12252
                                        · linarith only [h12169, h12252, hlam]
                                        · rcases p12207_3 (m.d 2 3) (by simp) with h12254 | h12254
                                          · rcases p12207_3 (m.d 2 4) (by simp) with h12255 | h12255
                                            · rcases p12207_3 (m.d 2 5) (by simp) with h12256 | h12256
                                              · rcases h3bigk with h12257c | h12257c | h12257c | h12257c | h12257c | h12257c | h12257c | h12257c | h12257c | h12257c | h12257c | h12257c | h12257c | h12257c | h12257c | h12257c | h12257c | h12257c | h12257c | h12257c | h12257c | h12257c | h12257c | h12257c | h12257c
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [hlam, p12257_0]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h11850, h12165, hc12, hc35, hlam, hphi, ht23, p12257_1]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h4, hlam, p12257_1]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h9250, hlam, p12257_0]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h11850, hlam, p12257_0]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h1, hlam, p12257_0]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [hlam, p12257_0]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h12165, hlam, p12257_1]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h12171, hlam, p12257_0]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h12173, hlam, p12257_0]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h1, h12165, hc12, hc23, hlam, hphi, p12257_1]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h12165, hc12, hc23, hlam, hphi, p12257_1]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [hlam, p12257_0]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h12175, h2, h9250, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p12257_1]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h1, h11850, h12165, hc12, hc23, hlam, hphi, p12257_1]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h1, h12165, hc12, hc34, hlam, hphi, ht23, p12257_1]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h12165, hc12, hc34, hlam, hphi, ht23, p12257_1]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h12176, hlam, p12257_0]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [hlam, p12257_0]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h1, h11850, h12165, h12176, hc12, hc23, hlam, hphi, p12257_1]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h1, h12165, hc12, hc35, hlam, hphi, ht23, p12257_1]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h12165, hc12, hc35, hlam, hphi, ht23, p12257_1]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h12177, hlam, p12257_0]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [h12179, hlam, p12257_0]
                                                · have p12257_0 := h12257c.1
                                                  have p12257_1 := h12257c.2.1
                                                  have p12257_2 := h12257c.2.2.1
                                                  have p12257_3 := h12257c.2.2.2
                                                  linarith only [hlam, p12257_0]
                                              · linarith only [h12256, hlam, p12207_0]
                                            · linarith only [h12255, h7337, hlam]
                                          · linarith only [h12254, h4, hlam]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      rcases p12207_3 (m.d 0 2) (by simp) with h12286 | h12286
                                      · linarith only [h12286, h8360, hlam]
                                      · linarith only [h0, h12286, hlam]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      linarith only [h12177, hlam, p12207_1]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      linarith only [h12178, hlam, p12207_0]
                                    · have p12207_0 := h12207c.1
                                      have p12207_1 := h12207c.2.1
                                      have p12207_2 := h12207c.2.2.1
                                      have p12207_3 := h12207c.2.2.2
                                      linarith only [hlam, p12207_0]
                          · linarith only [h12198, h2, hlam]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          rcases p12180_3 (m.d 0 1) (by simp) with h12293 | h12293
                          · rcases p12180_3 (m.d 0 2) (by simp) with h12294 | h12294
                            · linarith only [h0, h12294, hlam]
                            · rcases p12180_3 (m.d 0 3) (by simp) with h12296 | h12296
                              · linarith only [h1, h12296, hlam]
                              · rcases p12180_3 (m.d 0 4) (by simp) with h12298 | h12298
                                · linarith only [h12298, h2, hlam]
                                · linarith only [h12164, h12298, hlam]
                          · linarith only [h12293, h3, hlam]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [h0, hlam, p12180_0]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [hlam, p12180_0]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [h4, hlam, p12180_0]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [h7337, hlam, p12180_1]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [h8360, hlam, p12180_0]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [h1, hlam, p12180_1]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [h0, h12176, h9250, hc12, hc23, hlam, hphi, p12180_1]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [hlam, p12180_0]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [h9250, hlam, p12180_1]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [h11850, hlam, p12180_1]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [h2, hlam, p12180_0]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [h0, h12176, h9250, hc12, hc23, hlam, hphi, p12180_1]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [h1, h12165, h12176, h9250, hc12, hc23, hlam, hphi, p12180_1]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [hlam, p12180_0]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [h12165, h12173, h12176, h3, h9250, hc12, hc23, hlam, hphi, p12180_1]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [h3, hlam, p12180_0]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [h0, h11850, h12176, h12179, hc12, hc23, hlam, hphi, p12180_1]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [h1, h11850, h12165, h12176, h12179, hc12, hc23, hlam, hphi, p12180_1]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [h12164, hlam, p12180_1]
                        · have p12180_0 := h12180c.1
                          have p12180_1 := h12180c.2.1
                          have p12180_2 := h12180c.2.2.1
                          have p12180_3 := h12180c.2.2.2
                          linarith only [hlam, p12180_0]
                      · linarith only [h12175, h12179, h2, h9250, hlam]
                    · linarith only [h0, h12175, h12178, h2, h7337, h9250, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h12176, h12177, h9250, hc03, hc35, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12325 | h12325
                  · linarith only [h0, h11850, h12176, h12325, h4, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12327 | h12327
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12328 | h12328
                      · rcases h0bigk with h12329c | h12329c | h12329c | h12329c | h12329c | h12329c | h12329c | h12329c | h12329c | h12329c | h12329c | h12329c | h12329c | h12329c | h12329c | h12329c | h12329c | h12329c | h12329c | h12329c | h12329c | h12329c | h12329c | h12329c | h12329c
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          linarith only [hlam, p12329_0]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          rcases p12329_3 (m.d 0 1) (by simp) with h12331 | h12331
                          · rcases p12329_3 (m.d 0 2) (by simp) with h12332 | h12332
                            · linarith only [h0, h12332, hlam]
                            · rcases p12329_3 (m.d 0 3) (by simp) with h12334 | h12334
                              · linarith only [h1, h12334, hlam]
                              · linarith only [h12334, h4, hlam]
                          · linarith only [h0, h12331, hlam]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          rcases p12329_3 (m.d 0 1) (by simp) with h12338 | h12338
                          · rcases p12329_3 (m.d 0 2) (by simp) with h12339 | h12339
                            · linarith only [h0, h12339, hlam]
                            · rcases p12329_3 (m.d 0 3) (by simp) with h12341 | h12341
                              · linarith only [h1, h12341, hlam]
                              · rcases p12329_3 (m.d 0 4) (by simp) with h12343 | h12343
                                · linarith only [h12343, h2, hlam]
                                · linarith only [h12343, h9250, hlam]
                          · linarith only [h1, h12338, hlam]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          rcases p12329_3 (m.d 0 1) (by simp) with h12347 | h12347
                          · rcases p12329_3 (m.d 0 2) (by simp) with h12348 | h12348
                            · linarith only [h0, h12348, hlam]
                            · rcases p12329_3 (m.d 0 3) (by simp) with h12350 | h12350
                              · linarith only [h1, h12350, hlam]
                              · rcases p12329_3 (m.d 0 4) (by simp) with h12352 | h12352
                                · linarith only [h12352, h2, hlam]
                                · rcases p12329_3 (m.d 0 5) (by simp) with h12354 | h12354
                                  · linarith only [h12354, h3, hlam]
                                  · rcases h2bigk with h12356c | h12356c | h12356c | h12356c | h12356c | h12356c | h12356c | h12356c | h12356c | h12356c | h12356c | h12356c | h12356c | h12356c | h12356c | h12356c | h12356c | h12356c | h12356c | h12356c | h12356c | h12356c | h12356c | h12356c | h12356c
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [hlam, p12356_0]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [h12325, h12328, h4, hc12, hc34, hlam, hphi, ht23, p12356_1]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [h4, hlam, p12356_0]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [h7337, hlam, p12356_0]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [h8360, hlam, p12356_0]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [h0, hlam, p12356_0]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [hlam, p12356_0]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [h12165, hlam, p12356_0]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [h12167, hlam, p12356_0]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [h12169, hlam, p12356_0]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [h12325, h12328, hc02, hc34, hlam, hphi, ht23, p12356_1]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [h12325, h12328, hc12, hc34, hlam, hphi, ht23, p12356_1]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [hlam, p12356_0]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [h12176, hlam, p12356_0]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [h12325, hlam, p12356_0]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      rcases p12356_3 (m.d 0 2) (by simp) with h12372 | h12372
                                      · linarith only [h12372, hlam, p12356_0]
                                      · rcases p12356_3 (m.d 1 2) (by simp) with h12374 | h12374
                                        · linarith only [h12167, h12374, hlam]
                                        · rcases p12356_3 (m.d 2 3) (by simp) with h12376 | h12376
                                          · linarith only [h12176, h12376, hlam]
                                          · linarith only [h12376, h4, hlam]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      rcases p12356_3 (m.d 0 2) (by simp) with h12379 | h12379
                                      · linarith only [h12379, h7337, hlam]
                                      · linarith only [h0, h12379, hlam]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [h0, h12176, h4, hc12, hc34, hlam, hphi, ht23, p12356_1]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [hlam, p12356_0]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [h0, h12176, h8360, hc12, hc34, hlam, hphi, ht23, p12356_1]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      rcases p12356_3 (m.d 0 2) (by simp) with h12385 | h12385
                                      · linarith only [h12385, hlam, p12356_0]
                                      · rcases p12356_3 (m.d 1 2) (by simp) with h12387 | h12387
                                        · linarith only [h12169, h12387, hlam]
                                        · rcases p12356_3 (m.d 2 3) (by simp) with h12389 | h12389
                                          · linarith only [h12325, h12389, hlam]
                                          · linarith only [h12389, h4, hlam]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      rcases p12356_3 (m.d 0 2) (by simp) with h12392 | h12392
                                      · linarith only [h12392, h8360, hlam]
                                      · linarith only [h0, h12392, hlam]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p12356_1]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [h12327, hlam, p12356_0]
                                    · have p12356_0 := h12356c.1
                                      have p12356_1 := h12356c.2.1
                                      have p12356_2 := h12356c.2.2.1
                                      have p12356_3 := h12356c.2.2.2
                                      linarith only [hlam, p12356_0]
                          · linarith only [h12347, h2, hlam]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          rcases p12329_3 (m.d 0 1) (by simp) with h12399 | h12399
                          · rcases p12329_3 (m.d 0 2) (by simp) with h12400 | h12400
                            · linarith only [h0, h12400, hlam]
                            · rcases p12329_3 (m.d 0 3) (by simp) with h12402 | h12402
                              · linarith only [h1, h12402, hlam]
                              · rcases p12329_3 (m.d 0 4) (by simp) with h12404 | h12404
                                · linarith only [h12404, h2, hlam]
                                · linarith only [h12164, h12404, hlam]
                          · linarith only [h12399, h3, hlam]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          linarith only [h0, hlam, p12329_0]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          linarith only [hlam, p12329_0]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          linarith only [h4, hlam, p12329_0]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          linarith only [h7337, hlam, p12329_1]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          linarith only [h8360, hlam, p12329_0]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          linarith only [h1, hlam, p12329_1]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          linarith only [h0, h9250, hc12, hc34, hlam, hphi, ht23, p12329_1]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          linarith only [hlam, p12329_0]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          linarith only [h9250, hlam, p12329_1]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          linarith only [h11850, hlam, p12329_1]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          linarith only [h2, hlam, p12329_0]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          rcases p12329_3 (m.d 0 1) (by simp) with h12419 | h12419
                          · rcases p12329_3 (m.d 0 2) (by simp) with h12420 | h12420
                            · linarith only [h12420, h7337, hlam]
                            · rcases p12329_3 (m.d 0 3) (by simp) with h12422 | h12422
                              · linarith only [h12422, h9250, hlam]
                              · linarith only [h12422, h4, hlam]
                          · linarith only [h0, h12419, hlam]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          rcases p12329_3 (m.d 0 1) (by simp) with h12426 | h12426
                          · rcases p12329_3 (m.d 0 2) (by simp) with h12427 | h12427
                            · linarith only [h12427, h7337, hlam]
                            · rcases p12329_3 (m.d 0 3) (by simp) with h12429 | h12429
                              · linarith only [h12429, h9250, hlam]
                              · rcases p12329_3 (m.d 0 4) (by simp) with h12431 | h12431
                                · rcases p12329_3 (m.d 0 5) (by simp) with h12432 | h12432
                                  · linarith only [h12164, h12432, hlam]
                                  · linarith only [h11850, h12432, hlam]
                                · linarith only [h12431, h9250, hlam]
                          · linarith only [h1, h12426, hlam]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          linarith only [hlam, p12329_0]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          rcases p12329_3 (m.d 0 1) (by simp) with h12438 | h12438
                          · rcases p12329_3 (m.d 0 2) (by simp) with h12439 | h12439
                            · linarith only [h12439, h7337, hlam]
                            · rcases p12329_3 (m.d 0 3) (by simp) with h12441 | h12441
                              · linarith only [h12441, h9250, hlam]
                              · rcases p12329_3 (m.d 0 4) (by simp) with h12443 | h12443
                                · rcases p12329_3 (m.d 0 5) (by simp) with h12444 | h12444
                                  · linarith only [h12164, h12444, hlam]
                                  · rcases h2bigk with h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c | h12446c
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h12325, h12328, h4, hc12, hc34, hlam, hphi, ht23, p12446_1]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h4, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h7337, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h8360, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h0, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h12165, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h12167, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h12169, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h12325, h12328, hc02, hc34, hlam, hphi, ht23, p12446_1]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h12325, h12328, hc12, hc34, hlam, hphi, ht23, p12446_1]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h12176, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h12325, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      rcases p12446_3 (m.d 0 2) (by simp) with h12462 | h12462
                                      · linarith only [h12462, hlam, p12446_0]
                                      · rcases p12446_3 (m.d 1 2) (by simp) with h12464 | h12464
                                        · linarith only [h12167, h12464, hlam]
                                        · rcases p12446_3 (m.d 2 3) (by simp) with h12466 | h12466
                                          · linarith only [h12176, h12466, hlam]
                                          · linarith only [h12466, h4, hlam]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      rcases p12446_3 (m.d 0 2) (by simp) with h12469 | h12469
                                      · linarith only [h12469, h7337, hlam]
                                      · linarith only [h0, h12469, hlam]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h0, h12176, h4, hc12, hc34, hlam, hphi, ht23, p12446_1]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h0, h12176, h8360, hc12, hc34, hlam, hphi, ht23, p12446_1]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      rcases p12446_3 (m.d 0 2) (by simp) with h12475 | h12475
                                      · linarith only [h12475, hlam, p12446_0]
                                      · rcases p12446_3 (m.d 1 2) (by simp) with h12477 | h12477
                                        · linarith only [h12169, h12477, hlam]
                                        · rcases p12446_3 (m.d 2 3) (by simp) with h12479 | h12479
                                          · linarith only [h12325, h12479, hlam]
                                          · linarith only [h12479, h4, hlam]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      rcases p12446_3 (m.d 0 2) (by simp) with h12482 | h12482
                                      · linarith only [h12482, h8360, hlam]
                                      · linarith only [h0, h12482, hlam]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p12446_1]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [h12327, hlam, p12446_0]
                                    · have p12446_0 := h12446c.1
                                      have p12446_1 := h12446c.2.1
                                      have p12446_2 := h12446c.2.2.1
                                      have p12446_3 := h12446c.2.2.2
                                      linarith only [hlam, p12446_0]
                                · linarith only [h12164, h12443, hlam]
                          · linarith only [h12438, h3, hlam]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          linarith only [h3, hlam, p12329_0]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          rcases p12329_3 (m.d 0 1) (by simp) with h12491 | h12491
                          · rcases p12329_3 (m.d 0 2) (by simp) with h12492 | h12492
                            · linarith only [h12492, h8360, hlam]
                            · rcases p12329_3 (m.d 0 3) (by simp) with h12494 | h12494
                              · linarith only [h11850, h12494, hlam]
                              · linarith only [h12494, h4, hlam]
                          · linarith only [h0, h12491, hlam]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          rcases p12329_3 (m.d 0 1) (by simp) with h12498 | h12498
                          · rcases p12329_3 (m.d 0 2) (by simp) with h12499 | h12499
                            · linarith only [h12499, h8360, hlam]
                            · rcases p12329_3 (m.d 0 3) (by simp) with h12501 | h12501
                              · linarith only [h11850, h12501, hlam]
                              · rcases p12329_3 (m.d 0 4) (by simp) with h12503 | h12503
                                · rcases p12329_3 (m.d 0 5) (by simp) with h12504 | h12504
                                  · rcases h2bigk with h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c | h12505c
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [hlam, p12505_0]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [h4, hc12, hc23, hlam, hphi, p12505_1]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [h4, hlam, p12505_0]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [h7337, hlam, p12505_0]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [h8360, hlam, p12505_0]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [h0, hlam, p12505_0]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [hlam, p12505_0]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [h12165, hlam, p12505_0]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [h12167, hlam, p12505_0]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [h12169, hlam, p12505_0]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [h12176, hc02, hc34, hlam, hphi, ht23, p12505_1]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [h12176, hc12, hc34, hlam, hphi, ht23, p12505_1]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [hlam, p12505_0]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [h12176, hlam, p12505_0]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [h12325, hlam, p12505_0]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      rcases p12505_3 (m.d 0 2) (by simp) with h12521 | h12521
                                      · linarith only [h12521, hlam, p12505_0]
                                      · rcases p12505_3 (m.d 1 2) (by simp) with h12523 | h12523
                                        · linarith only [h12167, h12523, hlam]
                                        · rcases p12505_3 (m.d 2 3) (by simp) with h12525 | h12525
                                          · linarith only [h12176, h12525, hlam]
                                          · linarith only [h12525, h4, hlam]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      rcases p12505_3 (m.d 0 2) (by simp) with h12528 | h12528
                                      · linarith only [h12528, h7337, hlam]
                                      · linarith only [h0, h12528, hlam]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [h0, h12176, h4, hc12, hc34, hlam, hphi, ht23, p12505_1]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [hlam, p12505_0]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [h0, h12176, h8360, hc12, hc34, hlam, hphi, ht23, p12505_1]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      rcases p12505_3 (m.d 0 2) (by simp) with h12534 | h12534
                                      · linarith only [h12534, hlam, p12505_0]
                                      · rcases p12505_3 (m.d 1 2) (by simp) with h12536 | h12536
                                        · linarith only [h12169, h12536, hlam]
                                        · rcases p12505_3 (m.d 2 3) (by simp) with h12538 | h12538
                                          · linarith only [h12325, h12538, hlam]
                                          · linarith only [h12538, h4, hlam]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      rcases p12505_3 (m.d 0 2) (by simp) with h12541 | h12541
                                      · linarith only [h12541, h8360, hlam]
                                      · linarith only [h0, h12541, hlam]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p12505_1]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [h12327, hlam, p12505_0]
                                    · have p12505_0 := h12505c.1
                                      have p12505_1 := h12505c.2.1
                                      have p12505_2 := h12505c.2.2.1
                                      have p12505_3 := h12505c.2.2.2
                                      linarith only [hlam, p12505_0]
                                  · linarith only [h11850, h12504, hlam]
                                · linarith only [h12503, h9250, hlam]
                          · linarith only [h1, h12498, hlam]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          linarith only [h12164, hlam, p12329_1]
                        · have p12329_0 := h12329c.1
                          have p12329_1 := h12329c.2.1
                          have p12329_2 := h12329c.2.2.1
                          have p12329_3 := h12329c.2.2.2
                          linarith only [hlam, p12329_0]
                      · linarith only [h12175, h12176, h12328, h2, h7337, hlam]
                    · linarith only [h12175, h12327, h2, h7337, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h12554 | h12554
                · linarith only [h12164, h12165, h12171, h12175, h12554, h9250, hc12, hc23, hlam, hphi]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12556 | h12556
                  · linarith only [h0, h11850, h12554, h12556, h4, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12558 | h12558
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12559 | h12559
                      · rcases h0bigk with h12560c | h12560c | h12560c | h12560c | h12560c | h12560c | h12560c | h12560c | h12560c | h12560c | h12560c | h12560c | h12560c | h12560c | h12560c | h12560c | h12560c | h12560c | h12560c | h12560c | h12560c | h12560c | h12560c | h12560c | h12560c
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          linarith only [hlam, p12560_0]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          rcases p12560_3 (m.d 0 1) (by simp) with h12562 | h12562
                          · rcases p12560_3 (m.d 0 2) (by simp) with h12563 | h12563
                            · linarith only [h0, h12563, hlam]
                            · rcases p12560_3 (m.d 0 3) (by simp) with h12565 | h12565
                              · linarith only [h1, h12565, hlam]
                              · linarith only [h12565, h4, hlam]
                          · linarith only [h0, h12562, hlam]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          rcases p12560_3 (m.d 0 1) (by simp) with h12569 | h12569
                          · rcases p12560_3 (m.d 0 2) (by simp) with h12570 | h12570
                            · linarith only [h0, h12570, hlam]
                            · rcases p12560_3 (m.d 0 3) (by simp) with h12572 | h12572
                              · linarith only [h1, h12572, hlam]
                              · rcases p12560_3 (m.d 0 4) (by simp) with h12574 | h12574
                                · linarith only [h12574, h2, hlam]
                                · linarith only [h12574, h9250, hlam]
                          · linarith only [h1, h12569, hlam]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          linarith only [h12164, h12165, h12171, h12175, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12560_1]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          rcases p12560_3 (m.d 0 1) (by simp) with h12579 | h12579
                          · rcases p12560_3 (m.d 0 2) (by simp) with h12580 | h12580
                            · linarith only [h0, h12580, hlam]
                            · rcases p12560_3 (m.d 0 3) (by simp) with h12582 | h12582
                              · linarith only [h1, h12582, hlam]
                              · rcases p12560_3 (m.d 0 4) (by simp) with h12584 | h12584
                                · linarith only [h12584, h2, hlam]
                                · linarith only [h12164, h12584, hlam]
                          · linarith only [h12579, h3, hlam]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          linarith only [h0, hlam, p12560_0]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          linarith only [hlam, p12560_0]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          linarith only [h4, hlam, p12560_0]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          linarith only [h7337, hlam, p12560_1]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          linarith only [h8360, hlam, p12560_0]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          linarith only [h1, hlam, p12560_1]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          linarith only [h0, h9250, hc12, hc34, hlam, hphi, ht23, p12560_1]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          linarith only [hlam, p12560_0]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          linarith only [h9250, hlam, p12560_1]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          linarith only [h11850, hlam, p12560_1]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          linarith only [h2, hlam, p12560_0]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          rcases p12560_3 (m.d 0 1) (by simp) with h12599 | h12599
                          · rcases p12560_3 (m.d 0 2) (by simp) with h12600 | h12600
                            · linarith only [h12600, h7337, hlam]
                            · rcases p12560_3 (m.d 0 3) (by simp) with h12602 | h12602
                              · linarith only [h12602, h9250, hlam]
                              · linarith only [h12602, h4, hlam]
                          · linarith only [h0, h12599, hlam]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          rcases p12560_3 (m.d 0 1) (by simp) with h12606 | h12606
                          · rcases p12560_3 (m.d 0 2) (by simp) with h12607 | h12607
                            · linarith only [h12607, h7337, hlam]
                            · rcases p12560_3 (m.d 0 3) (by simp) with h12609 | h12609
                              · linarith only [h12609, h9250, hlam]
                              · rcases p12560_3 (m.d 0 4) (by simp) with h12611 | h12611
                                · rcases p12560_3 (m.d 0 5) (by simp) with h12612 | h12612
                                  · linarith only [h12164, h12612, hlam]
                                  · linarith only [h11850, h12612, hlam]
                                · linarith only [h12611, h9250, hlam]
                          · linarith only [h1, h12606, hlam]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          linarith only [hlam, p12560_0]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          linarith only [h12164, h12165, h12171, h12175, h7337, hc12, hc24, hlam, hphi, p12560_1]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          linarith only [h3, hlam, p12560_0]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          rcases p12560_3 (m.d 0 1) (by simp) with h12620 | h12620
                          · rcases p12560_3 (m.d 0 2) (by simp) with h12621 | h12621
                            · linarith only [h12621, h8360, hlam]
                            · rcases p12560_3 (m.d 0 3) (by simp) with h12623 | h12623
                              · linarith only [h11850, h12623, hlam]
                              · linarith only [h12623, h4, hlam]
                          · linarith only [h0, h12620, hlam]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          rcases p12560_3 (m.d 0 1) (by simp) with h12627 | h12627
                          · rcases p12560_3 (m.d 0 2) (by simp) with h12628 | h12628
                            · linarith only [h12628, h8360, hlam]
                            · rcases p12560_3 (m.d 0 3) (by simp) with h12630 | h12630
                              · linarith only [h11850, h12630, hlam]
                              · rcases p12560_3 (m.d 0 4) (by simp) with h12632 | h12632
                                · rcases p12560_3 (m.d 0 5) (by simp) with h12633 | h12633
                                  · rcases h2bigk with h12634c | h12634c | h12634c | h12634c | h12634c | h12634c | h12634c | h12634c | h12634c | h12634c | h12634c | h12634c | h12634c | h12634c | h12634c | h12634c | h12634c | h12634c | h12634c | h12634c | h12634c | h12634c | h12634c | h12634c | h12634c
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [hlam, p12634_0]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [h12556, h12559, h4, hc12, hc34, hlam, hphi, ht23, p12634_1]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [h4, hlam, p12634_0]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [h7337, hlam, p12634_0]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [h8360, hlam, p12634_0]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [h0, hlam, p12634_0]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [hlam, p12634_0]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [h12165, hlam, p12634_0]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [h12167, hlam, p12634_0]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [h12169, hlam, p12634_0]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [h12556, h12559, hc02, hc34, hlam, hphi, ht23, p12634_1]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [h12556, h12559, hc12, hc34, hlam, hphi, ht23, p12634_1]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [hlam, p12634_0]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [h12554, hlam, p12634_0]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [h12556, hlam, p12634_0]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      rcases p12634_3 (m.d 0 2) (by simp) with h12650 | h12650
                                      · linarith only [h12650, hlam, p12634_0]
                                      · rcases p12634_3 (m.d 1 2) (by simp) with h12652 | h12652
                                        · linarith only [h12167, h12652, hlam]
                                        · rcases p12634_3 (m.d 2 3) (by simp) with h12654 | h12654
                                          · linarith only [h12554, h12654, hlam]
                                          · linarith only [h12654, h4, hlam]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      rcases p12634_3 (m.d 0 2) (by simp) with h12657 | h12657
                                      · linarith only [h12657, h7337, hlam]
                                      · linarith only [h0, h12657, hlam]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [h0, h12554, h4, hc12, hc34, hlam, hphi, ht23, p12634_1]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [hlam, p12634_0]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [h1, h12165, h12554, h8360, hc12, hc34, hlam, hphi, ht23, p12560_1, p12634_1]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      rcases p12634_3 (m.d 0 2) (by simp) with h12663 | h12663
                                      · linarith only [h12663, hlam, p12634_0]
                                      · rcases p12634_3 (m.d 1 2) (by simp) with h12665 | h12665
                                        · linarith only [h12169, h12665, hlam]
                                        · rcases p12634_3 (m.d 2 3) (by simp) with h12667 | h12667
                                          · linarith only [h12556, h12667, hlam]
                                          · linarith only [h12667, h4, hlam]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      rcases p12634_3 (m.d 0 2) (by simp) with h12670 | h12670
                                      · linarith only [h12670, h8360, hlam]
                                      · linarith only [h0, h12670, hlam]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p12634_1]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [h12558, hlam, p12634_0]
                                    · have p12634_0 := h12634c.1
                                      have p12634_1 := h12634c.2.1
                                      have p12634_2 := h12634c.2.2.1
                                      have p12634_3 := h12634c.2.2.2
                                      linarith only [hlam, p12634_0]
                                  · linarith only [h11850, h12633, hlam]
                                · linarith only [h12632, h9250, hlam]
                          · linarith only [h1, h12627, hlam]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          linarith only [h12164, hlam, p12560_1]
                        · have p12560_0 := h12560c.1
                          have p12560_1 := h12560c.2.1
                          have p12560_2 := h12560c.2.2.1
                          have p12560_3 := h12560c.2.2.2
                          linarith only [hlam, p12560_0]
                      · linarith only [h12164, h12554, h12559, h7337, hlam]
                    · linarith only [h12164, h12558, h7337, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h12683 | h12683
    · linarith only [h0, h12683, h4, hlam]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h12685 | h12685
      · linarith only [h0, h12685, h7337, hlam]
      · rcases m.htr 1 2 5 (by decide) (by decide) with h12687 | h12687
        · linarith only [h0, h12687, h8360, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h12689 | h12689
          · linarith only [h1, h12689, h9250, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h12691 | h12691
            · linarith only [h1, h11850, h12691, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h12693 | h12693
              · linarith only [h12164, h12693, h2, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h12695 | h12695
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12696 | h12696
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12697 | h12697
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12698 | h12698
                      · linarith only [h0, h12164, h12695, h12698, h7337, hc12, hc23, hlam, hphi]
                      · linarith only [h0, h12695, h12697, h12698, h4, h9250, hc12, hc23, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12701 | h12701
                      · linarith only [h0, h12697, h12701, h7337, hc12, hc34, hlam, hphi, ht23]
                      · rcases h0bigk with h12703c | h12703c | h12703c | h12703c | h12703c | h12703c | h12703c | h12703c | h12703c | h12703c | h12703c | h12703c | h12703c | h12703c | h12703c | h12703c | h12703c | h12703c | h12703c | h12703c | h12703c | h12703c | h12703c | h12703c | h12703c
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [hlam, p12703_0]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          rcases p12703_3 (m.d 0 1) (by simp) with h12705 | h12705
                          · rcases p12703_3 (m.d 0 2) (by simp) with h12706 | h12706
                            · linarith only [h0, h12706, hlam]
                            · rcases p12703_3 (m.d 0 3) (by simp) with h12708 | h12708
                              · linarith only [h1, h12708, hlam]
                              · linarith only [h12708, h4, hlam]
                          · linarith only [h0, h12705, hlam]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          rcases p12703_3 (m.d 0 1) (by simp) with h12712 | h12712
                          · rcases p12703_3 (m.d 0 2) (by simp) with h12713 | h12713
                            · linarith only [h0, h12713, hlam]
                            · rcases p12703_3 (m.d 0 3) (by simp) with h12715 | h12715
                              · linarith only [h1, h12715, hlam]
                              · rcases p12703_3 (m.d 0 4) (by simp) with h12717 | h12717
                                · linarith only [h12717, h2, hlam]
                                · linarith only [h12717, h9250, hlam]
                          · linarith only [h1, h12712, hlam]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          rcases p12703_3 (m.d 0 1) (by simp) with h12721 | h12721
                          · rcases p12703_3 (m.d 0 2) (by simp) with h12722 | h12722
                            · linarith only [h0, h12722, hlam]
                            · rcases p12703_3 (m.d 0 3) (by simp) with h12724 | h12724
                              · linarith only [h1, h12724, hlam]
                              · rcases p12703_3 (m.d 0 4) (by simp) with h12726 | h12726
                                · linarith only [h12726, h2, hlam]
                                · rcases p12703_3 (m.d 0 5) (by simp) with h12728 | h12728
                                  · linarith only [h12728, h3, hlam]
                                  · linarith only [h12164, h12728, hlam]
                          · linarith only [h12721, h2, hlam]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          rcases p12703_3 (m.d 0 1) (by simp) with h12732 | h12732
                          · rcases p12703_3 (m.d 0 2) (by simp) with h12733 | h12733
                            · linarith only [h0, h12733, hlam]
                            · rcases p12703_3 (m.d 0 3) (by simp) with h12735 | h12735
                              · linarith only [h1, h12735, hlam]
                              · rcases p12703_3 (m.d 0 4) (by simp) with h12737 | h12737
                                · linarith only [h12737, h2, hlam]
                                · rcases p12703_3 (m.d 0 5) (by simp) with h12739 | h12739
                                  · linarith only [h12739, h3, hlam]
                                  · rcases h2bigk with h12741c | h12741c | h12741c | h12741c | h12741c | h12741c | h12741c | h12741c | h12741c | h12741c | h12741c | h12741c | h12741c | h12741c | h12741c | h12741c | h12741c | h12741c | h12741c | h12741c | h12741c | h12741c | h12741c | h12741c | h12741c
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [hlam, p12741_0]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [h12164, h4, h9250, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p12703_1, p12741_1]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [h4, hlam, p12741_0]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [h7337, hlam, p12741_0]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [h8360, hlam, p12741_0]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [h0, hlam, p12741_0]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [hlam, p12741_0]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [h12683, hlam, p12741_0]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [h12685, hlam, p12741_0]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [h12687, hlam, p12741_0]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      rcases p12741_3 (m.d 0 2) (by simp) with h12752 | h12752
                                      · linarith only [h12752, hlam, p12741_0]
                                      · rcases p12741_3 (m.d 1 2) (by simp) with h12754 | h12754
                                        · linarith only [h12683, h12754, hlam]
                                        · rcases p12741_3 (m.d 2 3) (by simp) with h12756 | h12756
                                          · rcases p12741_3 (m.d 2 4) (by simp) with h12757 | h12757
                                            · linarith only [h12695, h12757, hlam]
                                            · linarith only [h12757, h7337, hlam]
                                          · linarith only [h12756, hlam, p12741_0]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      rcases p12741_3 (m.d 0 2) (by simp) with h12761 | h12761
                                      · linarith only [h12761, h4, hlam]
                                      · linarith only [h0, h12761, hlam]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [hlam, p12741_0]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [h12695, h4, h9250, hc02, hc23, hlam, hphi, p12741_1]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [h0, h8360, hc12, hc23, hlam, hphi, p12741_1]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [h0, h12697, hc12, hc45, hlam, hphi, ht23, ht34, p12741_1]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [h12697, hc12, hc45, hlam, hphi, ht23, ht34, p12741_1]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [h12695, hlam, p12741_1]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [hlam, p12741_0]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [h12697, hlam, p12741_1]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      rcases p12741_3 (m.d 0 2) (by simp) with h12772 | h12772
                                      · linarith only [h12772, hlam, p12741_0]
                                      · rcases p12741_3 (m.d 1 2) (by simp) with h12774 | h12774
                                        · linarith only [h12687, h12774, hlam]
                                        · rcases p12741_3 (m.d 2 3) (by simp) with h12776 | h12776
                                          · rcases p12741_3 (m.d 2 4) (by simp) with h12777 | h12777
                                            · linarith only [h12697, h12777, hlam]
                                            · linarith only [h12777, h7337, hlam]
                                          · linarith only [h12776, h4, hlam]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      rcases p12741_3 (m.d 0 2) (by simp) with h12781 | h12781
                                      · linarith only [h12781, h8360, hlam]
                                      · linarith only [h0, h12781, hlam]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [h12696, hlam, p12741_1]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [h0, h7337, hc12, hc25, hlam, hphi, p12741_1]
                                    · have p12741_0 := h12741c.1
                                      have p12741_1 := h12741c.2.1
                                      have p12741_2 := h12741c.2.2.1
                                      have p12741_3 := h12741c.2.2.2
                                      linarith only [hlam, p12741_0]
                          · linarith only [h12732, h3, hlam]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [h0, hlam, p12703_0]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [hlam, p12703_0]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [h4, hlam, p12703_0]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [h7337, hlam, p12703_1]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [h8360, hlam, p12703_0]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [h1, hlam, p12703_1]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [h0, h9250, hc12, hc34, hlam, hphi, ht23, p12703_1]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [hlam, p12703_0]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [h9250, hlam, p12703_1]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [h11850, hlam, p12703_1]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [h2, hlam, p12703_0]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [h0, h12164, hc12, hc45, hlam, hphi, ht23, ht34, p12703_1]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [h1, h12164, h12683, hc12, hc45, hlam, hphi, ht23, ht34, p12703_1]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [hlam, p12703_0]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [h12164, hlam, p12703_0]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [h3, hlam, p12703_0]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [h0, h11850, h12696, hc12, hc23, hlam, hphi, p12703_1]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [h1, h11850, h12683, h12696, hc12, hc23, hlam, hphi, p12703_1]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [h11850, h12683, h12689, h12696, h2, hc12, hc23, hlam, hphi, p12703_1]
                        · have p12703_0 := h12703c.1
                          have p12703_1 := h12703c.2.1
                          have p12703_2 := h12703c.2.2.1
                          have p12703_3 := h12703c.2.2.2
                          linarith only [hlam, p12703_0]
                  · linarith only [h1, h12683, h12695, h12696, h9250, hc12, hc35, hlam, hphi, ht23]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h12809 | h12809
                  · linarith only [h1, h11850, h12683, h12695, h12809, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h12811 | h12811
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12812 | h12812
                      · rcases h0bigk with h12813c | h12813c | h12813c | h12813c | h12813c | h12813c | h12813c | h12813c | h12813c | h12813c | h12813c | h12813c | h12813c | h12813c | h12813c | h12813c | h12813c | h12813c | h12813c | h12813c | h12813c | h12813c | h12813c | h12813c | h12813c
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [hlam, p12813_0]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          rcases p12813_3 (m.d 0 1) (by simp) with h12815 | h12815
                          · rcases p12813_3 (m.d 0 2) (by simp) with h12816 | h12816
                            · linarith only [h0, h12816, hlam]
                            · rcases p12813_3 (m.d 0 3) (by simp) with h12818 | h12818
                              · linarith only [h1, h12818, hlam]
                              · linarith only [h12818, h4, hlam]
                          · linarith only [h0, h12815, hlam]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          rcases p12813_3 (m.d 0 1) (by simp) with h12822 | h12822
                          · rcases p12813_3 (m.d 0 2) (by simp) with h12823 | h12823
                            · linarith only [h0, h12823, hlam]
                            · rcases p12813_3 (m.d 0 3) (by simp) with h12825 | h12825
                              · linarith only [h1, h12825, hlam]
                              · rcases p12813_3 (m.d 0 4) (by simp) with h12827 | h12827
                                · linarith only [h12827, h2, hlam]
                                · linarith only [h12827, h9250, hlam]
                          · linarith only [h1, h12822, hlam]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          rcases p12813_3 (m.d 0 1) (by simp) with h12831 | h12831
                          · rcases p12813_3 (m.d 0 2) (by simp) with h12832 | h12832
                            · linarith only [h0, h12832, hlam]
                            · rcases p12813_3 (m.d 0 3) (by simp) with h12834 | h12834
                              · linarith only [h1, h12834, hlam]
                              · rcases p12813_3 (m.d 0 4) (by simp) with h12836 | h12836
                                · linarith only [h12836, h2, hlam]
                                · rcases p12813_3 (m.d 0 5) (by simp) with h12838 | h12838
                                  · linarith only [h12838, h3, hlam]
                                  · linarith only [h12164, h12838, hlam]
                          · linarith only [h12831, h2, hlam]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          rcases p12813_3 (m.d 0 1) (by simp) with h12842 | h12842
                          · rcases p12813_3 (m.d 0 2) (by simp) with h12843 | h12843
                            · linarith only [h0, h12843, hlam]
                            · rcases p12813_3 (m.d 0 3) (by simp) with h12845 | h12845
                              · linarith only [h1, h12845, hlam]
                              · rcases p12813_3 (m.d 0 4) (by simp) with h12847 | h12847
                                · linarith only [h12847, h2, hlam]
                                · rcases p12813_3 (m.d 0 5) (by simp) with h12849 | h12849
                                  · linarith only [h12849, h3, hlam]
                                  · rcases h2bigk with h12851c | h12851c | h12851c | h12851c | h12851c | h12851c | h12851c | h12851c | h12851c | h12851c | h12851c | h12851c | h12851c | h12851c | h12851c | h12851c | h12851c | h12851c | h12851c | h12851c | h12851c | h12851c | h12851c | h12851c | h12851c
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [hlam, p12851_0]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [h12809, h12812, h4, hc12, hc34, hlam, hphi, ht23, p12851_1]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [h4, hlam, p12851_0]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [h7337, hlam, p12851_0]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [h8360, hlam, p12851_0]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [h0, hlam, p12851_0]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [hlam, p12851_0]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [h12683, hlam, p12851_0]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [h12685, hlam, p12851_0]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [h12687, hlam, p12851_0]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [h12809, h12812, hc02, hc34, hlam, hphi, ht23, p12851_1]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [h12809, h12812, hc12, hc34, hlam, hphi, ht23, p12851_1]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [hlam, p12851_0]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [h12695, hlam, p12851_0]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [h12809, hlam, p12851_0]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      rcases p12851_3 (m.d 0 2) (by simp) with h12867 | h12867
                                      · linarith only [h12867, hlam, p12851_0]
                                      · rcases p12851_3 (m.d 1 2) (by simp) with h12869 | h12869
                                        · linarith only [h12685, h12869, hlam]
                                        · rcases p12851_3 (m.d 2 3) (by simp) with h12871 | h12871
                                          · linarith only [h12695, h12871, hlam]
                                          · linarith only [h12871, h4, hlam]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      rcases p12851_3 (m.d 0 2) (by simp) with h12874 | h12874
                                      · linarith only [h12874, h7337, hlam]
                                      · linarith only [h0, h12874, hlam]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [h0, h12695, h4, hc12, hc34, hlam, hphi, ht23, p12851_1]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [hlam, p12851_0]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [h0, h12695, h8360, hc12, hc34, hlam, hphi, ht23, p12851_1]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      rcases p12851_3 (m.d 0 2) (by simp) with h12880 | h12880
                                      · linarith only [h12880, hlam, p12851_0]
                                      · rcases p12851_3 (m.d 1 2) (by simp) with h12882 | h12882
                                        · linarith only [h12687, h12882, hlam]
                                        · rcases p12851_3 (m.d 2 3) (by simp) with h12884 | h12884
                                          · linarith only [h12809, h12884, hlam]
                                          · linarith only [h12884, h4, hlam]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      rcases p12851_3 (m.d 0 2) (by simp) with h12887 | h12887
                                      · linarith only [h12887, h8360, hlam]
                                      · linarith only [h0, h12887, hlam]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [h0, h4, hc12, hc25, hlam, hphi, p12851_1]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [h12811, hlam, p12851_0]
                                    · have p12851_0 := h12851c.1
                                      have p12851_1 := h12851c.2.1
                                      have p12851_2 := h12851c.2.2.1
                                      have p12851_3 := h12851c.2.2.2
                                      linarith only [hlam, p12851_0]
                          · linarith only [h12842, h3, hlam]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [h0, hlam, p12813_0]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [hlam, p12813_0]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [h4, hlam, p12813_0]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [h7337, hlam, p12813_1]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [h8360, hlam, p12813_0]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [h1, hlam, p12813_1]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [h0, h9250, hc12, hc34, hlam, hphi, ht23, p12813_1]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [hlam, p12813_0]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [h9250, hlam, p12813_1]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [h11850, hlam, p12813_1]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [h2, hlam, p12813_0]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [h0, h12164, h12695, h12811, hc12, hc34, hlam, hphi, ht23, p12813_1]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [h12164, h12695, h12811, hc03, hc34, hlam, hphi, p12813_1]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [hlam, p12813_0]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [h12164, hlam, p12813_0]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [h3, hlam, p12813_0]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [h0, h12164, h12695, h12811, hc12, hc34, hlam, hphi, ht23, p12813_1]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [h1, h12164, h12683, h12695, h12811, hc12, hc34, hlam, hphi, ht23, p12813_1]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [h12164, h12683, h12689, h12695, h12811, h2, hc12, hc34, hlam, hphi, ht23, p12813_1]
                        · have p12813_0 := h12813c.1
                          have p12813_1 := h12813c.2.1
                          have p12813_2 := h12813c.2.2.1
                          have p12813_3 := h12813c.2.2.2
                          linarith only [hlam, p12813_0]
                      · linarith only [h12695, h12811, h12812, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h12915 | h12915
                      · linarith only [h0, h12811, h12915, h7337, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h0, h12695, h12915, h4, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 7336000 in
set_option maxHeartbeats 7336000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s12_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (h9250 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  rcases m.htr 0 3 5 (by decide) (by decide) with h11850 | h11850
  · exact r1l7_10_12_23_L_I_L_I_H_I_s12_x1_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 hg8360 h9250 h11850
  · exact r1l7_10_12_23_L_I_L_I_H_I_s12_x1_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 hg8360 h9250 h11850

set_option maxHeartbeats 7336000 in
set_option maxHeartbeats 7336000 in
theorem r1l7_10_12_23_L_I_L_I_H_I_s12 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7337 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg8360 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7337 := hg7337
  have h8360 := hg8360
  rcases m.htr 0 3 4 (by decide) (by decide) with h9250 | h9250
  · exact r1l7_10_12_23_L_I_L_I_H_I_s12_x0 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 hg8360 h9250
  · exact r1l7_10_12_23_L_I_L_I_H_I_s12_x1 m hb0 hb2 hb3 hg0 hg1 hg2 hg3 hg4 hg7337 hg8360 h9250

end R2N4
