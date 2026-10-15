import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S36

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 39478000 in
set_option maxHeartbeats 39478000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s4 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s5 m hb1 hb2 hb4 hb5 h0 h1 h2 h3 h4 h5
  · rcases m.htr 0 2 5 (by decide) (by decide) with h19190 | h19190
    · rcases m.htr 0 3 4 (by decide) (by decide) with h19191 | h19191
      · linarith only [h19191, h4, h5, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h19193 | h19193
        · rcases m.htr 0 4 5 (by decide) (by decide) with h19194 | h19194
          · rcases m.htr 1 2 3 (by decide) (by decide) with h19195 | h19195
            · rcases m.htr 1 2 4 (by decide) (by decide) with h19196 | h19196
              · linarith only [h0, h19196, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h19198 | h19198
                · rcases m.htr 1 3 4 (by decide) (by decide) with h19199 | h19199
                  · linarith only [h1, h19191, h19193, h19199, hc01, hc35, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h19201 | h19201
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h19202 | h19202
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h19203 | h19203
                        · linarith only [h0, h1, h19191, h19195, h19201, h19203, hc02, hc35, hlam, hphi, ht0b, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h19205 | h19205
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h19206 | h19206
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h19207 | h19207
                              · rcases h1bigk with h19208c | h19208c | h19208c | h19208c | h19208c | h19208c | h19208c | h19208c | h19208c | h19208c | h19208c | h19208c | h19208c | h19208c | h19208c | h19208c | h19208c | h19208c | h19208c | h19208c | h19208c | h19208c | h19208c | h19208c | h19208c
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [hlam, p19208_0]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [h19195, h19205, h19207, hc01, hc45, hlam, hphi, ht0b, ht5b, p19208_1]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  rcases p19208_3 (m.d 0 1) (by simp) with h19211 | h19211
                                  · rcases p19208_3 (m.d 1 2) (by simp) with h19212 | h19212
                                    · linarith only [h0, h19212, hlam]
                                    · linarith only [h19195, h19212, hlam]
                                  · linarith only [h19211, hlam, p19208_0]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [h19195, h19196, h19205, h19207, hc01, hc45, hlam, hphi, ht0b, ht5b, p19208_1]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  rcases p19208_3 (m.d 0 1) (by simp) with h19217 | h19217
                                  · rcases p19208_3 (m.d 1 2) (by simp) with h19218 | h19218
                                    · linarith only [h0, h19218, hlam]
                                    · linarith only [h19198, h19218, hlam]
                                  · linarith only [h19217, hlam, p19208_0]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [h0, hlam, p19208_0]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [hlam, p19208_0]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [h0, h19195, h19205, h19207, hc01, hc45, hlam, hphi, ht0b, ht5b, p19208_1]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [h19196, hlam, p19208_1]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  rcases p19208_3 (m.d 0 1) (by simp) with h19226 | h19226
                                  · rcases p19208_3 (m.d 1 2) (by simp) with h19227 | h19227
                                    · rcases p19208_3 (m.d 1 3) (by simp) with h19228 | h19228
                                      · linarith only [h19195, h19228, hlam]
                                      · linarith only [h19201, h19228, hlam]
                                    · linarith only [h19198, h19227, hlam]
                                  · linarith only [h19226, h3, hlam]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [h1, hlam, p19208_0]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [h19195, hlam, p19208_0]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [hlam, p19208_0]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [h19199, hlam, p19208_0]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  rcases p19208_3 (m.d 0 1) (by simp) with h19237 | h19237
                                  · rcases p19208_3 (m.d 1 2) (by simp) with h19238 | h19238
                                    · rcases p19208_3 (m.d 1 3) (by simp) with h19239 | h19239
                                      · rcases p19208_3 (m.d 1 4) (by simp) with h19240 | h19240
                                        · rcases p19208_3 (m.d 1 5) (by simp) with h19241 | h19241
                                          · linarith only [h19201, h19241, hlam]
                                          · rcases h1emax with h19243 | h19243 | h19243 | h19243 | h19243
                                            · linarith only [h1, h19198, h19205, h19207, h19243, hc45, hlam, hphi, ht01, ht0b, ht5b, p19208_1]
                                            · linarith only [h19195, h19198, h19205, h19207, h19243, hc45, hlam, hphi, ht01, ht0b, ht5b, p19208_1]
                                            · linarith only [h19198, h19205, h19207, h19243, hc45, hlam, hphi, ht01, ht0b, ht5b, p19208_1]
                                            · linarith only [h19195, h19196, h19198, h19205, h19207, h19243, hc45, hlam, hphi, ht01, ht0b, ht5b, p19208_1]
                                            · rcases h2bigk with h19248c | h19248c | h19248c | h19248c | h19248c | h19248c | h19248c | h19248c | h19248c | h19248c | h19248c | h19248c | h19248c | h19248c | h19248c | h19248c | h19248c | h19248c | h19248c | h19248c | h19248c | h19248c | h19248c | h19248c | h19248c
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [hlam, p19248_0]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [h19195, h19198, h19203, h19205, h19207, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19208_1, p19248_1]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [h19203, h19205, h19207, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19248_1]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [h5, hlam, p19248_0]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                rcases p19248_3 (m.d 0 2) (by simp) with h19253 | h19253
                                                · rcases p19248_3 (m.d 1 2) (by simp) with h19254 | h19254
                                                  · linarith only [h0, h19254, hlam]
                                                  · linarith only [h19198, h19254, hlam]
                                                · linarith only [h19253, hlam, p19248_0]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [h0, hlam, p19248_1]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [hlam, p19248_0]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [h19196, h19205, h19207, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p19248_1]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [h19196, hlam, p19248_0]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                rcases p19248_3 (m.d 0 2) (by simp) with h19262 | h19262
                                                · rcases p19248_3 (m.d 1 2) (by simp) with h19263 | h19263
                                                  · rcases p19248_3 (m.d 2 3) (by simp) with h19264 | h19264
                                                    · linarith only [h19195, h19264, hlam]
                                                    · linarith only [h19205, h19264, hlam]
                                                  · linarith only [h19263, hlam, p19248_0]
                                                · linarith only [h19190, h19262, hlam]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [h4, hlam, p19248_0]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [h19195, hlam, p19248_0]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [hlam, p19248_0]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [h19203, hlam, p19248_1]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [h19203, h19205, h19207, h4, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p19248_1]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [h19203, h4, hc23, hc34, hlam, hphi, p19248_1]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [h19195, h19203, hc23, hc34, hlam, hphi, p19248_1]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                rcases p19248_3 (m.d 0 2) (by simp) with h19276 | h19276
                                                · linarith only [h19276, h5, hlam]
                                                · linarith only [h19276, h4, hlam]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [hlam, p19248_0]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [h1, h19198, h4, h5, hlam, p19208_1, p19248_2]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [h19190, hlam, p19248_0]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [h19198, hlam, p19248_0]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [h19205, hlam, p19248_0]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [h19206, hlam, p19248_1]
                                              · have p19248_0 := h19248c.1
                                                have p19248_1 := h19248c.2.1
                                                have p19248_2 := h19248c.2.2.1
                                                have p19248_3 := h19248c.2.2.2
                                                linarith only [hlam, p19248_0]
                                        · linarith only [h19202, h19240, hlam]
                                      · linarith only [h19201, h19239, hlam]
                                    · linarith only [h19198, h19238, hlam]
                                  · linarith only [h19237, h3, hlam]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [h2, hlam, p19208_0]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [h19195, h19205, h19207, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p19208_1]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [h19195, h19205, h19207, h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p19208_1]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [hlam, p19208_0]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  rcases p19208_3 (m.d 0 1) (by simp) with h19294 | h19294
                                  · rcases p19208_3 (m.d 1 2) (by simp) with h19295 | h19295
                                    · linarith only [h19196, h19295, hlam]
                                    · linarith only [h19198, h19295, hlam]
                                  · linarith only [h19294, h3, hlam]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [h3, hlam, p19208_0]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [h19198, hlam, p19208_0]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [h19201, hlam, p19208_0]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [h19202, hlam, p19208_0]
                                · have p19208_0 := h19208c.1
                                  have p19208_1 := h19208c.2.1
                                  have p19208_2 := h19208c.2.2.1
                                  have p19208_3 := h19208c.2.2.2
                                  linarith only [hlam, p19208_0]
                              · linarith only [h19191, h19194, h19207, hlam]
                            · linarith only [h0, h19195, h19205, h19206, h5, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h19193, h19203, h19205, h4, h5, hc23, hc34, hlam, hphi]
                      · linarith only [h19191, h19194, h19195, h19196, h19202, hc23, hc34, hlam, hphi]
                    · linarith only [h19191, h19193, h19201, hc13, hc34, hlam, hphi]
                · linarith only [h19190, h19195, h19198, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h19195, h4, h5, hc12, hc24, hlam, hphi]
          · linarith only [h19193, h19194, h4, h5, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h19312 | h19312
          · rcases m.htr 1 2 3 (by decide) (by decide) with h19313 | h19313
            · rcases m.htr 1 2 4 (by decide) (by decide) with h19314 | h19314
              · linarith only [h0, h19190, h19314, h5, hc01, hc25, hlam, hphi, ht0b, ht5b]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h19316 | h19316
                · rcases m.htr 1 3 4 (by decide) (by decide) with h19317 | h19317
                  · linarith only [h1, h19191, h19317, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h19319 | h19319
                    · linarith only [h1, h19193, h19319, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h19321 | h19321
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h19322 | h19322
                        · linarith only [h0, h19191, h19313, h19322, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h19324 | h19324
                          · linarith only [h1, h19193, h19313, h19324, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h19326 | h19326
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h19327 | h19327
                              · rcases h1bigk with h19328c | h19328c | h19328c | h19328c | h19328c | h19328c | h19328c | h19328c | h19328c | h19328c | h19328c | h19328c | h19328c | h19328c | h19328c | h19328c | h19328c | h19328c | h19328c | h19328c | h19328c | h19328c | h19328c | h19328c | h19328c
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  linarith only [hlam, p19328_0]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  rcases p19328_3 (m.d 0 1) (by simp) with h19330 | h19330
                                  · rcases p19328_3 (m.d 1 2) (by simp) with h19331 | h19331
                                    · linarith only [h19331, hlam, p19328_0]
                                    · rcases p19328_3 (m.d 1 3) (by simp) with h19333 | h19333
                                      · linarith only [h1, h19333, hlam]
                                      · rcases p19328_3 (m.d 1 4) (by simp) with h19335 | h19335
                                        · linarith only [h19335, h2, hlam]
                                        · linarith only [h19314, h19335, hlam]
                                  · linarith only [h19330, hlam, p19328_0]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  rcases p19328_3 (m.d 0 1) (by simp) with h19339 | h19339
                                  · rcases p19328_3 (m.d 1 2) (by simp) with h19340 | h19340
                                    · linarith only [h0, h19340, hlam]
                                    · linarith only [h19313, h19340, hlam]
                                  · linarith only [h19339, hlam, p19328_0]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  rcases p19328_3 (m.d 0 1) (by simp) with h19344 | h19344
                                  · rcases p19328_3 (m.d 1 2) (by simp) with h19345 | h19345
                                    · linarith only [h0, h19345, hlam]
                                    · rcases p19328_3 (m.d 1 3) (by simp) with h19347 | h19347
                                      · linarith only [h1, h19347, hlam]
                                      · rcases p19328_3 (m.d 1 4) (by simp) with h19349 | h19349
                                        · linarith only [h19349, hlam, p19328_0]
                                        · rcases p19328_3 (m.d 1 5) (by simp) with h19351 | h19351
                                          · linarith only [h19351, h3, hlam]
                                          · rcases h1emax with h19353 | h19353 | h19353 | h19353 | h19353
                                            · linarith only [h19314, h19353, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p19328_1]
                                            · rcases h2bigk with h19355c | h19355c | h19355c | h19355c | h19355c | h19355c | h19355c | h19355c | h19355c | h19355c | h19355c | h19355c | h19355c | h19355c | h19355c | h19355c | h19355c | h19355c | h19355c | h19355c | h19355c | h19355c | h19355c | h19355c | h19355c
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [hlam, p19355_0]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [h19316, h19324, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p19355_1]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [h19322, h5, hc23, hc34, hlam, hphi, p19355_1]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [h5, hlam, p19355_0]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [h19322, h19324, h5, hc23, hc34, hlam, hphi, p19355_1]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [h0, hlam, p19355_1]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [hlam, p19355_0]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [h19314, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19328_1, p19355_1]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [h19314, hlam, p19355_0]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [h19314, h19324, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19328_1, p19355_1]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [h4, hlam, p19355_0]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [h19313, hlam, p19355_0]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [hlam, p19355_0]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [h19322, hlam, p19355_1]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [h19324, hlam, p19355_1]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [h19322, h4, hc23, hc34, hlam, hphi, p19355_1]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [h19313, h19322, hc23, hc34, hlam, hphi, p19355_1]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                rcases p19355_3 (m.d 0 2) (by simp) with h19373 | h19373
                                                · linarith only [h19373, h5, hlam]
                                                · linarith only [h19373, h4, hlam]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [hlam, p19355_0]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                rcases p19355_3 (m.d 0 2) (by simp) with h19377 | h19377
                                                · linarith only [h19377, h5, hlam]
                                                · linarith only [h19190, h19377, hlam]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [h19190, hlam, p19355_0]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [h19316, hlam, p19355_0]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [h0, h19316, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19355_1]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [h19326, hlam, p19355_1]
                                              · have p19355_0 := h19355c.1
                                                have p19355_1 := h19355c.2.1
                                                have p19355_2 := h19355c.2.2.1
                                                have p19355_3 := h19355c.2.2.2
                                                linarith only [hlam, p19355_0]
                                            · rcases h2bigk with h19385c | h19385c | h19385c | h19385c | h19385c | h19385c | h19385c | h19385c | h19385c | h19385c | h19385c | h19385c | h19385c | h19385c | h19385c | h19385c | h19385c | h19385c | h19385c | h19385c | h19385c | h19385c | h19385c | h19385c | h19385c
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [hlam, p19385_0]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [h19322, h5, hc12, hc34, hlam, hphi, ht23, p19385_1]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [h19322, h5, hc23, hc34, hlam, hphi, p19385_1]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [h5, hlam, p19385_0]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [h19322, h19324, h5, hc23, hc34, hlam, hphi, p19385_1]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [h0, hlam, p19385_1]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [hlam, p19385_0]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [h0, h19322, h5, hc23, hc34, hlam, hphi, p19385_1]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [h19314, hlam, p19385_0]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [h19314, h19326, hc01, hc45, hlam, hphi, ht0b, ht5b, p19328_1, p19385_1]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [h4, hlam, p19385_0]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [h19313, hlam, p19385_0]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [hlam, p19385_0]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [h19322, hlam, p19385_1]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [h19324, hlam, p19385_1]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [h19322, h4, hc23, hc34, hlam, hphi, p19385_1]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [h19313, h19322, hc23, hc34, hlam, hphi, p19385_1]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                rcases p19385_3 (m.d 0 2) (by simp) with h19403 | h19403
                                                · linarith only [h19403, h5, hlam]
                                                · linarith only [h19403, h4, hlam]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [hlam, p19385_0]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                rcases p19385_3 (m.d 0 2) (by simp) with h19407 | h19407
                                                · linarith only [h19407, h5, hlam]
                                                · linarith only [h19190, h19407, hlam]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [h19190, hlam, p19385_0]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [h19316, hlam, p19385_0]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [h0, h19316, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19385_1]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [h19326, hlam, p19385_1]
                                              · have p19385_0 := h19385c.1
                                                have p19385_1 := h19385c.2.1
                                                have p19385_2 := h19385c.2.2.1
                                                have p19385_3 := h19385c.2.2.2
                                                linarith only [hlam, p19385_0]
                                            · rcases h2bigk with h19415c | h19415c | h19415c | h19415c | h19415c | h19415c | h19415c | h19415c | h19415c | h19415c | h19415c | h19415c | h19415c | h19415c | h19415c | h19415c | h19415c | h19415c | h19415c | h19415c | h19415c | h19415c | h19415c | h19415c | h19415c
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [hlam, p19415_0]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [h19322, h5, hc12, hc34, hlam, hphi, ht23, p19415_1]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [h19322, h5, hc23, hc34, hlam, hphi, p19415_1]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [h5, hlam, p19415_0]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [h19322, h19324, h5, hc23, hc34, hlam, hphi, p19415_1]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [h0, hlam, p19415_1]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [hlam, p19415_0]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [h0, h19322, h5, hc23, hc34, hlam, hphi, p19415_1]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [h19314, hlam, p19415_0]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [h19314, h19324, h19353, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19415_1]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [h4, hlam, p19415_0]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [h19313, hlam, p19415_0]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [hlam, p19415_0]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [h19322, hlam, p19415_1]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [h19324, hlam, p19415_1]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [h19322, h4, hc23, hc34, hlam, hphi, p19415_1]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [h19313, h19322, hc23, hc34, hlam, hphi, p19415_1]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                rcases p19415_3 (m.d 0 2) (by simp) with h19433 | h19433
                                                · linarith only [h19433, h5, hlam]
                                                · linarith only [h19433, h4, hlam]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [hlam, p19415_0]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                rcases p19415_3 (m.d 0 2) (by simp) with h19437 | h19437
                                                · linarith only [h19437, h5, hlam]
                                                · linarith only [h19190, h19437, hlam]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [h19190, hlam, p19415_0]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [h19316, hlam, p19415_0]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [h0, h19316, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19415_1]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [h19326, hlam, p19415_1]
                                              · have p19415_0 := h19415c.1
                                                have p19415_1 := h19415c.2.1
                                                have p19415_2 := h19415c.2.2.1
                                                have p19415_3 := h19415c.2.2.2
                                                linarith only [hlam, p19415_0]
                                            · rcases h2bigk with h19445c | h19445c | h19445c | h19445c | h19445c | h19445c | h19445c | h19445c | h19445c | h19445c | h19445c | h19445c | h19445c | h19445c | h19445c | h19445c | h19445c | h19445c | h19445c | h19445c | h19445c | h19445c | h19445c | h19445c | h19445c
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [hlam, p19445_0]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [h19322, h5, hc12, hc34, hlam, hphi, ht23, p19445_1]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [h19322, h5, hc23, hc34, hlam, hphi, p19445_1]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [h5, hlam, p19445_0]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [h19322, h19324, h5, hc23, hc34, hlam, hphi, p19445_1]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [h0, hlam, p19445_1]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [hlam, p19445_0]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [h0, h19322, h5, hc23, hc34, hlam, hphi, p19445_1]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [h19314, hlam, p19445_0]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [h19314, h19324, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19328_1, p19445_1]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [h4, hlam, p19445_0]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [h19313, hlam, p19445_0]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [hlam, p19445_0]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [h19322, hlam, p19445_1]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [h19324, hlam, p19445_1]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [h19322, h4, hc23, hc34, hlam, hphi, p19445_1]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [h19313, h19322, hc23, hc34, hlam, hphi, p19445_1]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                rcases p19445_3 (m.d 0 2) (by simp) with h19463 | h19463
                                                · linarith only [h19463, h5, hlam]
                                                · linarith only [h19463, h4, hlam]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [hlam, p19445_0]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                rcases p19445_3 (m.d 0 2) (by simp) with h19467 | h19467
                                                · linarith only [h19467, h5, hlam]
                                                · linarith only [h19190, h19467, hlam]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [h19190, hlam, p19445_0]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [h19316, hlam, p19445_0]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [h0, h19316, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19445_1]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [h19326, hlam, p19445_1]
                                              · have p19445_0 := h19445c.1
                                                have p19445_1 := h19445c.2.1
                                                have p19445_2 := h19445c.2.2.1
                                                have p19445_3 := h19445c.2.2.2
                                                linarith only [hlam, p19445_0]
                                  · linarith only [h19344, hlam, p19328_0]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  rcases p19328_3 (m.d 0 1) (by simp) with h19476 | h19476
                                  · rcases p19328_3 (m.d 1 2) (by simp) with h19477 | h19477
                                    · linarith only [h0, h19477, hlam]
                                    · linarith only [h19316, h19477, hlam]
                                  · linarith only [h19476, hlam, p19328_0]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  linarith only [h0, hlam, p19328_0]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  linarith only [hlam, p19328_0]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  linarith only [h0, h19313, h19322, h5, hc23, hc34, hlam, hphi, p19328_1]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  linarith only [h19314, hlam, p19328_1]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  linarith only [h0, h19313, h19319, h19322, h5, hc23, hc34, hlam, hphi, p19328_1]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  linarith only [h1, hlam, p19328_0]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  linarith only [h19313, hlam, p19328_0]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  linarith only [hlam, p19328_0]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  linarith only [h19317, hlam, p19328_0]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  linarith only [h19319, hlam, p19328_1]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  linarith only [h2, hlam, p19328_0]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  linarith only [h19313, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19328_1]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  rcases p19328_3 (m.d 0 1) (by simp) with h19493 | h19493
                                  · rcases p19328_3 (m.d 1 2) (by simp) with h19494 | h19494
                                    · linarith only [h19314, h19494, hlam]
                                    · linarith only [h19313, h19494, hlam]
                                  · linarith only [h1, h19493, hlam]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  linarith only [hlam, p19328_0]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  rcases p19328_3 (m.d 0 1) (by simp) with h19499 | h19499
                                  · rcases p19328_3 (m.d 1 2) (by simp) with h19500 | h19500
                                    · linarith only [h19314, h19500, hlam]
                                    · linarith only [h19316, h19500, hlam]
                                  · linarith only [h19499, h3, hlam]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  linarith only [h3, hlam, p19328_0]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  linarith only [h19316, hlam, p19328_0]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  linarith only [h19190, h19313, h19322, h3, h5, hc23, hc34, hlam, hphi, p19328_1]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  linarith only [h19321, hlam, p19328_0]
                                · have p19328_0 := h19328c.1
                                  have p19328_1 := h19328c.2.1
                                  have p19328_2 := h19328c.2.2.1
                                  have p19328_3 := h19328c.2.2.2
                                  linarith only [hlam, p19328_0]
                              · linarith only [h19322, h19327, h4, h5, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h19190, h19321, h19326, h3, h5, hlam]
                      · linarith only [h19191, h19312, h19313, h19314, h19321, hc23, hc34, hlam, hphi]
                · linarith only [h19190, h19313, h19316, h5, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
            · linarith only [h19313, h4, h5, hc12, hc24, hlam, hphi]
          · linarith only [h19190, h19312, h5, hlam]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h19515 | h19515
      · linarith only [h19515, h4, h5, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h19517 | h19517
        · linarith only [h19190, h19517, h4, hlam]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h19519 | h19519
          · rcases m.htr 1 2 3 (by decide) (by decide) with h19520 | h19520
            · rcases m.htr 1 2 4 (by decide) (by decide) with h19521 | h19521
              · linarith only [h0, h19521, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h19523 | h19523
                · linarith only [h0, h19190, h19523, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h19525 | h19525
                  · linarith only [h1, h19515, h19525, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h19527 | h19527
                    · linarith only [h1, h19190, h19517, h19527, h4, hlam]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h19529 | h19529
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h19530 | h19530
                        · linarith only [h0, h1, h19515, h19520, h19530, h5, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h19532 | h19532
                          · linarith only [h19190, h19517, h19532, h4, hlam]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h19534 | h19534
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h19535 | h19535
                              · rcases h1bigk with h19536c | h19536c | h19536c | h19536c | h19536c | h19536c | h19536c | h19536c | h19536c | h19536c | h19536c | h19536c | h19536c | h19536c | h19536c | h19536c | h19536c | h19536c | h19536c | h19536c | h19536c | h19536c | h19536c | h19536c | h19536c
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  linarith only [hlam, p19536_0]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  rcases p19536_3 (m.d 0 1) (by simp) with h19538 | h19538
                                  · rcases p19536_3 (m.d 1 2) (by simp) with h19539 | h19539
                                    · linarith only [h19539, hlam, p19536_0]
                                    · rcases p19536_3 (m.d 1 3) (by simp) with h19541 | h19541
                                      · linarith only [h1, h19541, hlam]
                                      · rcases p19536_3 (m.d 1 4) (by simp) with h19543 | h19543
                                        · linarith only [h19543, h2, hlam]
                                        · linarith only [h19521, h19543, hlam]
                                  · linarith only [h19538, hlam, p19536_0]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  rcases p19536_3 (m.d 0 1) (by simp) with h19547 | h19547
                                  · rcases p19536_3 (m.d 1 2) (by simp) with h19548 | h19548
                                    · linarith only [h0, h19548, hlam]
                                    · linarith only [h19520, h19548, hlam]
                                  · linarith only [h19547, hlam, p19536_0]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  rcases p19536_3 (m.d 0 1) (by simp) with h19552 | h19552
                                  · rcases p19536_3 (m.d 1 2) (by simp) with h19553 | h19553
                                    · linarith only [h0, h19553, hlam]
                                    · rcases p19536_3 (m.d 1 3) (by simp) with h19555 | h19555
                                      · linarith only [h1, h19555, hlam]
                                      · rcases p19536_3 (m.d 1 4) (by simp) with h19557 | h19557
                                        · linarith only [h19557, hlam, p19536_0]
                                        · rcases p19536_3 (m.d 1 5) (by simp) with h19559 | h19559
                                          · linarith only [h19559, h3, hlam]
                                          · rcases h1emax with h19561 | h19561 | h19561 | h19561 | h19561
                                            · linarith only [h0, h19520, h19561, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                                            · rcases h2bigk with h19563c | h19563c | h19563c | h19563c | h19563c | h19563c | h19563c | h19563c | h19563c | h19563c | h19563c | h19563c | h19563c | h19563c | h19563c | h19563c | h19563c | h19563c | h19563c | h19563c | h19563c | h19563c | h19563c | h19563c | h19563c
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [hlam, p19563_0]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [h19190, h19520, h19534, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p19563_1]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [h19190, h19530, h19534, hc23, hc34, hlam, hphi, p19563_1]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [h5, hlam, p19563_0]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [h19190, hlam, p19563_0]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [h0, hlam, p19563_1]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [hlam, p19563_0]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [h0, h19190, h19530, h19534, hc23, hc34, hlam, hphi, p19563_1]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [h19521, hlam, p19563_0]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [h19523, hlam, p19563_0]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [h4, hlam, p19563_0]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [h19520, hlam, p19563_0]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [hlam, p19563_0]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [h19530, hlam, p19563_1]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [h19532, hlam, p19563_1]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [h19530, h4, hc23, hc34, hlam, hphi, p19563_1]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [h19520, h19530, hc23, hc34, hlam, hphi, p19563_1]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                rcases p19563_3 (m.d 0 2) (by simp) with h19581 | h19581
                                                · linarith only [h19581, h5, hlam]
                                                · linarith only [h19581, h4, hlam]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [hlam, p19563_0]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [h0, h19190, h19520, h19530, hc23, hc34, hlam, hphi, p19563_1]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [h0, h19520, h19532, hc23, hc35, hlam, hphi, p19563_1]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [h19520, h19532, hc23, hc35, hlam, hphi, p19563_1]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                rcases p19563_3 (m.d 0 2) (by simp) with h19588 | h19588
                                                · linarith only [h19190, h19588, hlam]
                                                · linarith only [h19588, h4, hlam]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [h19534, hlam, p19563_1]
                                              · have p19563_0 := h19563c.1
                                                have p19563_1 := h19563c.2.1
                                                have p19563_2 := h19563c.2.2.1
                                                have p19563_3 := h19563c.2.2.2
                                                linarith only [hlam, p19563_0]
                                            · rcases h2bigk with h19593c | h19593c | h19593c | h19593c | h19593c | h19593c | h19593c | h19593c | h19593c | h19593c | h19593c | h19593c | h19593c | h19593c | h19593c | h19593c | h19593c | h19593c | h19593c | h19593c | h19593c | h19593c | h19593c | h19593c | h19593c
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [hlam, p19593_0]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [h19520, h19530, h5, hc23, hc34, hlam, hphi, p19593_1]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [h19530, h5, hc23, hc34, hlam, hphi, p19593_1]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [h5, hlam, p19593_0]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [h19190, hlam, p19593_0]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [h0, hlam, p19593_1]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [hlam, p19593_0]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [h0, h19530, h5, hc23, hc34, hlam, hphi, p19593_1]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [h19521, hlam, p19593_0]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [h19523, hlam, p19593_0]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [h4, hlam, p19593_0]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [h19520, hlam, p19593_0]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [hlam, p19593_0]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [h19530, hlam, p19593_1]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [h19532, hlam, p19593_1]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [h19530, h4, hc23, hc34, hlam, hphi, p19593_1]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [h19520, h19530, hc23, hc34, hlam, hphi, p19593_1]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                rcases p19593_3 (m.d 0 2) (by simp) with h19611 | h19611
                                                · linarith only [h19611, h5, hlam]
                                                · linarith only [h19611, h4, hlam]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [hlam, p19593_0]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [h0, h19190, h19520, h19530, hc23, hc34, hlam, hphi, p19593_1]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [h0, h19520, h19532, h19535, hc23, hc34, hlam, hphi, p19593_1]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [h19520, h19532, h19535, hc23, hc34, hlam, hphi, p19593_1]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                rcases p19593_3 (m.d 0 2) (by simp) with h19618 | h19618
                                                · linarith only [h19190, h19618, hlam]
                                                · linarith only [h19618, h4, hlam]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [h19534, hlam, p19593_1]
                                              · have p19593_0 := h19593c.1
                                                have p19593_1 := h19593c.2.1
                                                have p19593_2 := h19593c.2.2.1
                                                have p19593_3 := h19593c.2.2.2
                                                linarith only [hlam, p19593_0]
                                            · rcases h2bigk with h19623c | h19623c | h19623c | h19623c | h19623c | h19623c | h19623c | h19623c | h19623c | h19623c | h19623c | h19623c | h19623c | h19623c | h19623c | h19623c | h19623c | h19623c | h19623c | h19623c | h19623c | h19623c | h19623c | h19623c | h19623c
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [hlam, p19623_0]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [h19520, h19530, h5, hc23, hc34, hlam, hphi, p19623_1]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [h19530, h5, hc23, hc34, hlam, hphi, p19623_1]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [h5, hlam, p19623_0]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [h19190, hlam, p19623_0]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [h0, hlam, p19623_1]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [hlam, p19623_0]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [h19523, h19529, h19561, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p19623_1]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [h19521, hlam, p19623_0]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [h19523, hlam, p19623_0]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [h4, hlam, p19623_0]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [h19520, hlam, p19623_0]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [hlam, p19623_0]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [h19530, hlam, p19623_1]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [h19532, hlam, p19623_1]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [h19530, h4, hc23, hc34, hlam, hphi, p19623_1]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [h19520, h19530, hc23, hc34, hlam, hphi, p19623_1]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                rcases p19623_3 (m.d 0 2) (by simp) with h19641 | h19641
                                                · linarith only [h19641, h5, hlam]
                                                · linarith only [h19641, h4, hlam]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [hlam, p19623_0]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [h0, h19190, h19520, h19530, hc23, hc34, hlam, hphi, p19623_1]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [h0, h19520, h19532, h19535, hc23, hc34, hlam, hphi, p19623_1]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [h19520, h19532, h19535, hc23, hc34, hlam, hphi, p19623_1]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                rcases p19623_3 (m.d 0 2) (by simp) with h19648 | h19648
                                                · linarith only [h19190, h19648, hlam]
                                                · linarith only [h19648, h4, hlam]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [h19534, hlam, p19623_1]
                                              · have p19623_0 := h19623c.1
                                                have p19623_1 := h19623c.2.1
                                                have p19623_2 := h19623c.2.2.1
                                                have p19623_3 := h19623c.2.2.2
                                                linarith only [hlam, p19623_0]
                                            · rcases h2bigk with h19653c | h19653c | h19653c | h19653c | h19653c | h19653c | h19653c | h19653c | h19653c | h19653c | h19653c | h19653c | h19653c | h19653c | h19653c | h19653c | h19653c | h19653c | h19653c | h19653c | h19653c | h19653c | h19653c | h19653c | h19653c
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [hlam, p19653_0]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [h19520, h19530, h5, hc23, hc34, hlam, hphi, p19653_1]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [h19530, h5, hc23, hc34, hlam, hphi, p19653_1]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [h5, hlam, p19653_0]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [h19190, hlam, p19653_0]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [h0, hlam, p19653_1]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [hlam, p19653_0]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [h0, h19530, h5, hc23, hc34, hlam, hphi, p19653_1]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [h19521, hlam, p19653_0]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [h19523, hlam, p19653_0]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [h4, hlam, p19653_0]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [h19520, hlam, p19653_0]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [hlam, p19653_0]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [h19530, hlam, p19653_1]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [h19532, hlam, p19653_1]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [h19530, h4, hc23, hc34, hlam, hphi, p19653_1]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [h19520, h19530, hc23, hc34, hlam, hphi, p19653_1]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                rcases p19653_3 (m.d 0 2) (by simp) with h19671 | h19671
                                                · linarith only [h19671, h5, hlam]
                                                · linarith only [h19671, h4, hlam]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [hlam, p19653_0]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [h0, h19190, h19520, h19530, hc23, hc34, hlam, hphi, p19653_1]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [h0, h19520, h19532, h19535, hc23, hc34, hlam, hphi, p19653_1]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [h19520, h19532, h19535, hc23, hc34, hlam, hphi, p19653_1]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                rcases p19653_3 (m.d 0 2) (by simp) with h19678 | h19678
                                                · linarith only [h19190, h19678, hlam]
                                                · linarith only [h19678, h4, hlam]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [h19534, hlam, p19653_1]
                                              · have p19653_0 := h19653c.1
                                                have p19653_1 := h19653c.2.1
                                                have p19653_2 := h19653c.2.2.1
                                                have p19653_3 := h19653c.2.2.2
                                                linarith only [hlam, p19653_0]
                                  · linarith only [h19552, hlam, p19536_0]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  rcases p19536_3 (m.d 0 1) (by simp) with h19684 | h19684
                                  · rcases p19536_3 (m.d 1 2) (by simp) with h19685 | h19685
                                    · linarith only [h0, h19685, hlam]
                                    · rcases p19536_3 (m.d 1 3) (by simp) with h19687 | h19687
                                      · linarith only [h1, h19687, hlam]
                                      · rcases p19536_3 (m.d 1 4) (by simp) with h19689 | h19689
                                        · linarith only [h19689, h2, hlam]
                                        · linarith only [h19529, h19689, hlam]
                                  · linarith only [h19684, hlam, p19536_0]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  linarith only [h0, hlam, p19536_0]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  linarith only [hlam, p19536_0]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  linarith only [h0, h19530, h5, hc13, hc34, hlam, hphi, p19536_1]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  linarith only [h19521, hlam, p19536_1]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  linarith only [h19523, hlam, p19536_1]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  linarith only [h1, hlam, p19536_0]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  linarith only [h19520, hlam, p19536_0]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  linarith only [hlam, p19536_0]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  linarith only [h19525, hlam, p19536_0]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  linarith only [h19527, hlam, p19536_1]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  linarith only [h2, hlam, p19536_0]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  linarith only [h19520, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19536_1]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  rcases p19536_3 (m.d 0 1) (by simp) with h19705 | h19705
                                  · rcases p19536_3 (m.d 1 2) (by simp) with h19706 | h19706
                                    · linarith only [h19521, h19706, hlam]
                                    · linarith only [h19520, h19706, hlam]
                                  · linarith only [h1, h19705, hlam]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  linarith only [hlam, p19536_0]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  linarith only [h19520, h19523, h2, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19536_1]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  linarith only [h3, hlam, p19536_0]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  linarith only [h19520, h3, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p19536_1]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  rcases p19536_3 (m.d 0 1) (by simp) with h19714 | h19714
                                  · rcases p19536_3 (m.d 1 2) (by simp) with h19715 | h19715
                                    · linarith only [h19523, h19715, hlam]
                                    · linarith only [h19520, h19715, hlam]
                                  · linarith only [h1, h19714, hlam]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  linarith only [h19529, hlam, p19536_0]
                                · have p19536_0 := h19536c.1
                                  have p19536_1 := h19536c.2.1
                                  have p19536_2 := h19536c.2.2.1
                                  have p19536_3 := h19536c.2.2.2
                                  linarith only [hlam, p19536_0]
                              · linarith only [h0, h19520, h19530, h19535, h5, hc23, hc45, hlam, hphi, ht34]
                            · linarith only [h19529, h19534, h2, h5, hlam]
                      · linarith only [h19515, h19519, h19520, h19521, h19529, hc23, hc34, hlam, hphi]
            · linarith only [h19520, h4, h5, hc12, hc24, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h19725 | h19725
            · rcases m.htr 1 2 4 (by decide) (by decide) with h19726 | h19726
              · linarith only [h0, h19726, h5, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h19728 | h19728
                · linarith only [h0, h19190, h19728, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h19730 | h19730
                  · linarith only [h1, h19515, h19730, hlam]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h19732 | h19732
                    · linarith only [h1, h19515, h19517, h19519, h19732, h4, h5, hc23, hc34, hlam, hphi]
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h19734 | h19734
                      · linarith only [h0, h19519, h19725, h19734, h2, h5, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h19736 | h19736
                        · linarith only [h0, h19519, h19725, h19736, h5, hc34, hc45, hlam, hphi]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h19738 | h19738
                          · linarith only [h0, h19517, h19519, h19725, h19738, h5, hc03, hc45, hlam, hphi, ht34]
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h19740 | h19740
                            · linarith only [h19519, h19736, h19740, h4, h5, hc23, hc34, hlam, hphi]
                            · linarith only [h0, h19725, h19740, h5, hc23, hc45, hlam, hphi, ht34]
            · linarith only [h19725, h4, h5, hc12, hc24, hlam, hphi]

end R2N4
