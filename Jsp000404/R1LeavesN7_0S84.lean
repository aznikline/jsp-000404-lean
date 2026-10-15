import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_0S83

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h39231 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  rcases m.htr 0 3 5 (by decide) (by decide) with h40175 | h40175
  · rcases m.htr 0 4 5 (by decide) (by decide) with h40176 | h40176
    · rcases m.htr 1 2 3 (by decide) (by decide) with h40177 | h40177
      · rcases m.htr 1 2 4 (by decide) (by decide) with h40178 | h40178
        · rcases m.htr 1 2 5 (by decide) (by decide) with h40179 | h40179
          · rcases m.htr 1 3 4 (by decide) (by decide) with h40180 | h40180
            · rcases m.htr 1 3 5 (by decide) (by decide) with h40181 | h40181
              · rcases m.htr 1 4 5 (by decide) (by decide) with h40182 | h40182
                · rcases m.htr 2 3 4 (by decide) (by decide) with h40183 | h40183
                  · linarith only [h33187, h39227, h39228, h39231, h40183, hc02, hc15, hlam, hphi, ht0b, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h40185 | h40185
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h40186 | h40186
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h40187 | h40187
                        · rcases h1bigk with h40188c | h40188c | h40188c | h40188c | h40188c | h40188c | h40188c | h40188c | h40188c | h40188c | h40188c | h40188c | h40188c | h40188c | h40188c | h40188c | h40188c | h40188c | h40188c | h40188c | h40188c | h40188c | h40188c | h40188c | h40188c
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [hlam, p40188_0]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [h0, hlam, p40188_0]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [h33187, hlam, p40188_0]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [h36828, hlam, p40188_0]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [h33187, h39231, h40179, h40180, h40185, h40187, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p40188_1]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            rcases p40188_3 (m.d 0 1) (by simp) with h40194 | h40194
                            · linarith only [h40194, hlam, p40188_0]
                            · rcases p40188_3 (m.d 1 2) (by simp) with h40196 | h40196
                              · rcases p40188_3 (m.d 1 3) (by simp) with h40197 | h40197
                                · linarith only [h40177, h40197, hlam]
                                · linarith only [h33187, h40197, hlam]
                              · linarith only [h40196, hlam, p40188_0]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [hlam, p40188_0]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [h33187, h39231, h40180, hc01, hc12, hlam, hphi, p40188_1]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [h33187, h39227, h39231, h40179, h40180, h40185, h40187, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40188_1]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [h33187, h39227, h39231, h40177, h40180, hlam, p40188_2]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            rcases p40188_3 (m.d 0 1) (by simp) with h40205 | h40205
                            · linarith only [h40205, hlam, p40188_0]
                            · rcases p40188_3 (m.d 1 2) (by simp) with h40207 | h40207
                              · rcases p40188_3 (m.d 1 3) (by simp) with h40208 | h40208
                                · rcases p40188_3 (m.d 1 4) (by simp) with h40209 | h40209
                                  · linarith only [h40180, h40209, hlam]
                                  · linarith only [h36828, h40209, hlam]
                                · linarith only [h40208, hlam, p40188_0]
                              · linarith only [h0, h40207, hlam]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [h40177, hlam, p40188_0]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [hlam, p40188_0]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [h33187, h39227, h39231, h40177, h40179, h40180, h40185, h40187, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40188_1]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [h33187, h39227, h39231, h40180, hlam, p40188_2]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            rcases p40188_3 (m.d 0 1) (by simp) with h40218 | h40218
                            · linarith only [h40218, hlam, p40188_0]
                            · rcases p40188_3 (m.d 1 2) (by simp) with h40220 | h40220
                              · rcases p40188_3 (m.d 1 3) (by simp) with h40221 | h40221
                                · rcases p40188_3 (m.d 1 4) (by simp) with h40222 | h40222
                                  · rcases p40188_3 (m.d 1 5) (by simp) with h40223 | h40223
                                    · linarith only [h40182, h40223, hlam]
                                    · rcases h1emax with h40225 | h40225 | h40225 | h40225 | h40225
                                      · rcases h2bigk with h40226c | h40226c | h40226c | h40226c | h40226c | h40226c | h40226c | h40226c | h40226c | h40226c | h40226c | h40226c | h40226c | h40226c | h40226c | h40226c | h40226c | h40226c | h40226c | h40226c | h40226c | h40226c | h40226c | h40226c | h40226c
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          linarith only [hlam, p40226_0]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          linarith only [h0, hlam, p40226_0]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          rcases p40226_3 (m.d 0 2) (by simp) with h40229 | h40229
                                          · rcases p40226_3 (m.d 1 2) (by simp) with h40230 | h40230
                                            · rcases p40226_3 (m.d 2 3) (by simp) with h40231 | h40231
                                              · linarith only [h40231, hlam, p40226_0]
                                              · rcases p40226_3 (m.d 2 4) (by simp) with h40233 | h40233
                                                · linarith only [h39229, h40233, hlam]
                                                · linarith only [h40183, h40233, hlam]
                                            · linarith only [h40177, h40230, hlam]
                                          · linarith only [h40229, hlam, p40226_0]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          rcases p40226_3 (m.d 0 2) (by simp) with h40238 | h40238
                                          · rcases p40226_3 (m.d 1 2) (by simp) with h40239 | h40239
                                            · rcases p40226_3 (m.d 2 3) (by simp) with h40240 | h40240
                                              · linarith only [h39228, h40240, hlam]
                                              · rcases p40226_3 (m.d 2 4) (by simp) with h40242 | h40242
                                                · linarith only [h40242, hlam, p40226_0]
                                                · rcases p40226_3 (m.d 2 5) (by simp) with h40244 | h40244
                                                  · linarith only [h39230, h40244, hlam]
                                                  · rcases h4bigk with h40246c | h40246c | h40246c | h40246c | h40246c | h40246c | h40246c | h40246c | h40246c | h40246c | h40246c | h40246c | h40246c | h40246c | h40246c | h40246c | h40246c | h40246c | h40246c | h40246c | h40246c | h40246c | h40246c | h40246c | h40246c
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [hlam, p40246_0]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [h36828, hlam, p40246_1]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [h39231, h40180, h40183, h40185, h40187, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p40246_1]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [h39231, hlam, p40246_1]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      rcases p40246_3 (m.d 0 4) (by simp) with h40251 | h40251
                                                      · rcases p40246_3 (m.d 1 4) (by simp) with h40252 | h40252
                                                        · rcases p40246_3 (m.d 2 4) (by simp) with h40253 | h40253
                                                          · linarith only [h39229, h40253, hlam]
                                                          · linarith only [h40186, h40253, hlam]
                                                        · linarith only [h40182, h40252, hlam]
                                                      · linarith only [h40251, hlam, p40246_0]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      rcases p40246_3 (m.d 0 4) (by simp) with h40258 | h40258
                                                      · linarith only [h36828, h40258, hlam]
                                                      · rcases p40246_3 (m.d 1 4) (by simp) with h40260 | h40260
                                                        · rcases p40246_3 (m.d 2 4) (by simp) with h40261 | h40261
                                                          · linarith only [h40178, h40261, hlam]
                                                          · rcases p40246_3 (m.d 3 4) (by simp) with h40263 | h40263
                                                            · linarith only [h40180, h40263, hlam]
                                                            · linarith only [h39231, h40263, hlam]
                                                        · linarith only [h36828, h40260, hlam]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [hlam, p40246_0]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      rcases p40246_3 (m.d 0 4) (by simp) with h40268 | h40268
                                                      · linarith only [h36828, h40268, hlam]
                                                      · linarith only [h39229, h40268, hlam]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [h33187, h39227, h39231, h40177, h40179, h40180, h40185, h40187, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40246_1]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [h39227, h40179, h40185, h40187, hlam, p40188_1, p40246_2]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [h39229, hlam, p40246_0]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [h40178, hlam, p40246_0]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [hlam, p40246_0]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [h40183, hlam, p40246_1]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40226_1, p40246_1]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [h33187, h39227, h39231, h40177, h40179, h40180, h40185, h40187, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40246_1]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [h40180, hlam, p40246_0]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [h40177, h40180, h40183, h40185, h40187, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40246_1]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [hlam, p40246_0]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      rcases p40246_3 (m.d 0 4) (by simp) with h40282 | h40282
                                                      · linarith only [h39231, h40282, hlam]
                                                      · linarith only [h40176, h40282, hlam]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [h40176, hlam, p40246_0]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [h40182, hlam, p40246_0]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [h40186, hlam, p40246_0]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [h40187, hlam, p40246_0]
                                                    · have p40246_0 := h40246c.1
                                                      have p40246_1 := h40246c.2.1
                                                      have p40246_2 := h40246c.2.2.1
                                                      have p40246_3 := h40246c.2.2.2
                                                      linarith only [hlam, p40246_0]
                                            · linarith only [h40178, h40239, hlam]
                                          · linarith only [h40238, hlam, p40226_0]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          rcases p40226_3 (m.d 0 2) (by simp) with h40292 | h40292
                                          · rcases p40226_3 (m.d 1 2) (by simp) with h40293 | h40293
                                            · rcases p40226_3 (m.d 2 3) (by simp) with h40294 | h40294
                                              · linarith only [h39228, h40294, hlam]
                                              · linarith only [h40185, h40294, hlam]
                                            · linarith only [h40179, h40293, hlam]
                                          · linarith only [h40292, hlam, p40226_0]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          linarith only [h39228, h40185, h40187, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40226_1]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          linarith only [hlam, p40226_0]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          rcases p40226_3 (m.d 0 2) (by simp) with h40301 | h40301
                                          · linarith only [h0, h40301, hlam]
                                          · linarith only [h39228, h40301, hlam]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          rcases p40226_3 (m.d 0 2) (by simp) with h40304 | h40304
                                          · linarith only [h0, h40304, hlam]
                                          · linarith only [h39229, h40304, hlam]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          linarith only [h33187, h39227, h39231, h40177, h40179, h40180, hlam, p40226_2]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          linarith only [h39228, hlam, p40226_0]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          linarith only [h40177, hlam, p40226_0]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          linarith only [hlam, p40226_0]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          linarith only [h40183, hlam, p40226_1]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          linarith only [h39228, h39231, h40177, h40180, h40185, h40187, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40226_1]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          linarith only [h39229, hlam, p40226_0]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          linarith only [h40178, hlam, p40226_0]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          linarith only [h39229, h39231, h40177, h40180, h40185, h40187, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40226_1]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          linarith only [hlam, p40226_0]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          rcases p40226_3 (m.d 0 2) (by simp) with h40317 | h40317
                                          · rcases p40226_3 (m.d 1 2) (by simp) with h40318 | h40318
                                            · rcases p40226_3 (m.d 2 3) (by simp) with h40319 | h40319
                                              · linarith only [h40183, h40319, hlam]
                                              · linarith only [h40185, h40319, hlam]
                                            · linarith only [h40179, h40318, hlam]
                                          · linarith only [h39230, h40317, hlam]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          linarith only [h39230, hlam, p40226_0]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          linarith only [h40179, hlam, p40226_0]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          linarith only [h40185, hlam, p40226_0]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          linarith only [h40186, hlam, p40226_1]
                                        · have p40226_0 := h40226c.1
                                          have p40226_1 := h40226c.2.1
                                          have p40226_2 := h40226c.2.2.1
                                          have p40226_3 := h40226c.2.2.2
                                          linarith only [hlam, p40226_0]
                                      · linarith only [h0, h39227, h40179, h40185, h40187, h40225, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                      · linarith only [h33187, h39227, h39231, h40179, h40180, h40185, h40187, h40225, hc45, hlam, hphi, ht01, ht0b, ht5b]
                                      · linarith only [h39227, h40179, h40185, h40187, h40225, hc45, hlam, hphi, ht01, ht0b, ht5b, p40188_1]
                                      · rcases h2bigk with h40332c | h40332c | h40332c | h40332c | h40332c | h40332c | h40332c | h40332c | h40332c | h40332c | h40332c | h40332c | h40332c | h40332c | h40332c | h40332c | h40332c | h40332c | h40332c | h40332c | h40332c | h40332c | h40332c | h40332c | h40332c
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          linarith only [hlam, p40332_0]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          linarith only [h0, hlam, p40332_0]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          rcases p40332_3 (m.d 0 2) (by simp) with h40335 | h40335
                                          · rcases p40332_3 (m.d 1 2) (by simp) with h40336 | h40336
                                            · rcases p40332_3 (m.d 2 3) (by simp) with h40337 | h40337
                                              · linarith only [h40337, hlam, p40332_0]
                                              · rcases p40332_3 (m.d 2 4) (by simp) with h40339 | h40339
                                                · linarith only [h39229, h40339, hlam]
                                                · linarith only [h40183, h40339, hlam]
                                            · linarith only [h40177, h40336, hlam]
                                          · linarith only [h40335, hlam, p40332_0]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          rcases p40332_3 (m.d 0 2) (by simp) with h40344 | h40344
                                          · rcases p40332_3 (m.d 1 2) (by simp) with h40345 | h40345
                                            · rcases p40332_3 (m.d 2 3) (by simp) with h40346 | h40346
                                              · linarith only [h39228, h40346, hlam]
                                              · rcases p40332_3 (m.d 2 4) (by simp) with h40348 | h40348
                                                · linarith only [h40348, hlam, p40332_0]
                                                · rcases p40332_3 (m.d 2 5) (by simp) with h40350 | h40350
                                                  · linarith only [h39230, h40350, hlam]
                                                  · rcases h4bigk with h40352c | h40352c | h40352c | h40352c | h40352c | h40352c | h40352c | h40352c | h40352c | h40352c | h40352c | h40352c | h40352c | h40352c | h40352c | h40352c | h40352c | h40352c | h40352c | h40352c | h40352c | h40352c | h40352c | h40352c | h40352c
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [hlam, p40352_0]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [h36828, hlam, p40352_1]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [h39231, h40177, h40180, h40183, h40185, h40187, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40352_1]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [h39231, hlam, p40352_1]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      rcases p40352_3 (m.d 0 4) (by simp) with h40357 | h40357
                                                      · rcases p40352_3 (m.d 1 4) (by simp) with h40358 | h40358
                                                        · rcases p40352_3 (m.d 2 4) (by simp) with h40359 | h40359
                                                          · linarith only [h39229, h40359, hlam]
                                                          · linarith only [h40186, h40359, hlam]
                                                        · linarith only [h40182, h40358, hlam]
                                                      · linarith only [h40357, hlam, p40352_0]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      rcases p40352_3 (m.d 0 4) (by simp) with h40364 | h40364
                                                      · linarith only [h36828, h40364, hlam]
                                                      · rcases p40352_3 (m.d 1 4) (by simp) with h40366 | h40366
                                                        · rcases p40352_3 (m.d 2 4) (by simp) with h40367 | h40367
                                                          · linarith only [h40178, h40367, hlam]
                                                          · rcases p40352_3 (m.d 3 4) (by simp) with h40369 | h40369
                                                            · linarith only [h40180, h40369, hlam]
                                                            · linarith only [h39231, h40369, hlam]
                                                        · linarith only [h36828, h40366, hlam]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [hlam, p40352_0]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      rcases p40352_3 (m.d 0 4) (by simp) with h40374 | h40374
                                                      · linarith only [h36828, h40374, hlam]
                                                      · linarith only [h39229, h40374, hlam]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [h33187, h39227, h39231, h40179, h40185, h40187, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p40352_1]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [h39227, h40179, h40185, h40187, hlam, p40188_1, p40352_2]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [h39229, hlam, p40352_0]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [h40178, hlam, p40352_0]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [hlam, p40352_0]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [h40183, hlam, p40352_1]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [h0, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40332_1, p40352_1]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [h33187, h39227, h39231, h40177, h40179, h40180, h40185, h40187, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40352_1]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [h40180, hlam, p40352_0]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [h40177, h40180, h40183, h40185, h40187, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40352_1]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [hlam, p40352_0]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      rcases p40352_3 (m.d 0 4) (by simp) with h40388 | h40388
                                                      · linarith only [h39231, h40388, hlam]
                                                      · linarith only [h40176, h40388, hlam]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [h40176, hlam, p40352_0]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [h40182, hlam, p40352_0]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [h40186, hlam, p40352_0]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [h40187, hlam, p40352_0]
                                                    · have p40352_0 := h40352c.1
                                                      have p40352_1 := h40352c.2.1
                                                      have p40352_2 := h40352c.2.2.1
                                                      have p40352_3 := h40352c.2.2.2
                                                      linarith only [hlam, p40352_0]
                                            · linarith only [h40178, h40345, hlam]
                                          · linarith only [h40344, hlam, p40332_0]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          rcases p40332_3 (m.d 0 2) (by simp) with h40398 | h40398
                                          · rcases p40332_3 (m.d 1 2) (by simp) with h40399 | h40399
                                            · rcases p40332_3 (m.d 2 3) (by simp) with h40400 | h40400
                                              · linarith only [h39228, h40400, hlam]
                                              · linarith only [h40185, h40400, hlam]
                                            · linarith only [h40179, h40399, hlam]
                                          · linarith only [h40398, hlam, p40332_0]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          linarith only [h39228, h40185, h40187, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40332_1]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          linarith only [hlam, p40332_0]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          rcases p40332_3 (m.d 0 2) (by simp) with h40407 | h40407
                                          · linarith only [h0, h40407, hlam]
                                          · linarith only [h39228, h40407, hlam]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          rcases p40332_3 (m.d 0 2) (by simp) with h40410 | h40410
                                          · linarith only [h0, h40410, hlam]
                                          · linarith only [h39229, h40410, hlam]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          linarith only [h33187, h39227, h39231, h40177, h40179, h40180, hlam, p40332_2]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          linarith only [h39228, hlam, p40332_0]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          linarith only [h40177, hlam, p40332_0]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          linarith only [hlam, p40332_0]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          linarith only [h40183, hlam, p40332_1]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          linarith only [h39228, h39231, h40177, h40180, h40185, h40187, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40332_1]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          linarith only [h39229, hlam, p40332_0]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          linarith only [h40178, hlam, p40332_0]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          linarith only [h39229, h39231, h40177, h40180, h40185, h40187, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40332_1]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          linarith only [hlam, p40332_0]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          rcases p40332_3 (m.d 0 2) (by simp) with h40423 | h40423
                                          · rcases p40332_3 (m.d 1 2) (by simp) with h40424 | h40424
                                            · rcases p40332_3 (m.d 2 3) (by simp) with h40425 | h40425
                                              · linarith only [h40183, h40425, hlam]
                                              · linarith only [h40185, h40425, hlam]
                                            · linarith only [h40179, h40424, hlam]
                                          · linarith only [h39230, h40423, hlam]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          linarith only [h39230, hlam, p40332_0]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          linarith only [h40179, hlam, p40332_0]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          linarith only [h40185, hlam, p40332_0]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          linarith only [h40186, hlam, p40332_1]
                                        · have p40332_0 := h40332c.1
                                          have p40332_1 := h40332c.2.1
                                          have p40332_2 := h40332c.2.2.1
                                          have p40332_3 := h40332c.2.2.2
                                          linarith only [hlam, p40332_0]
                                  · linarith only [h40222, hlam, p40188_0]
                                · linarith only [h33187, h40221, hlam]
                              · linarith only [h0, h40220, hlam]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [h40178, hlam, p40188_0]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [h40180, hlam, p40188_1]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [hlam, p40188_0]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            rcases p40188_3 (m.d 0 1) (by simp) with h40441 | h40441
                            · linarith only [h36828, h40441, hlam]
                            · linarith only [h39227, h40441, hlam]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [h39227, hlam, p40188_0]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [h40179, hlam, p40188_0]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [h40181, hlam, p40188_0]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [h40182, hlam, p40188_0]
                          · have p40188_0 := h40188c.1
                            have p40188_1 := h40188c.2.1
                            have p40188_2 := h40188c.2.2.1
                            have p40188_3 := h40188c.2.2.2
                            linarith only [hlam, p40188_0]
                        · linarith only [h33187, h39227, h39231, h40176, h40179, h40185, h40187, hc04, hc35, hlam, hphi, ht0b, ht5b]
                      · linarith only [h33187, h39227, h39231, h40177, h40180, h40182, h40186, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h39231, h40175, h40177, h40180, h40185, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                · linarith only [h36828, h40176, h40182, hlam]
              · linarith only [h33187, h39231, h40180, h40181, hc01, hc35, hlam, hphi, ht12, ht23]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h40454 | h40454
              · rcases m.htr 1 4 5 (by decide) (by decide) with h40455 | h40455
                · rcases m.htr 2 3 4 (by decide) (by decide) with h40456 | h40456
                  · linarith only [h33187, h39227, h40179, h40180, h40456, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h40458 | h40458
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h40459 | h40459
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h40460 | h40460
                        · rcases h1bigk with h40461c | h40461c | h40461c | h40461c | h40461c | h40461c | h40461c | h40461c | h40461c | h40461c | h40461c | h40461c | h40461c | h40461c | h40461c | h40461c | h40461c | h40461c | h40461c | h40461c | h40461c | h40461c | h40461c | h40461c | h40461c
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [hlam, p40461_0]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [h0, hlam, p40461_0]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [h33187, hlam, p40461_0]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [h36828, hlam, p40461_0]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [h33187, h40179, h40180, h40458, h40460, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p40461_1]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            rcases p40461_3 (m.d 0 1) (by simp) with h40467 | h40467
                            · linarith only [h40467, hlam, p40461_0]
                            · rcases p40461_3 (m.d 1 2) (by simp) with h40469 | h40469
                              · rcases p40461_3 (m.d 1 3) (by simp) with h40470 | h40470
                                · linarith only [h40177, h40470, hlam]
                                · linarith only [h33187, h40470, hlam]
                              · linarith only [h40469, hlam, p40461_0]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [hlam, p40461_0]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [h33187, hc01, hc12, hlam, hphi, p40461_1]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [h36828, h39227, h40179, h40458, h40460, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40461_1]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            rcases p40461_3 (m.d 0 1) (by simp) with h40477 | h40477
                            · linarith only [h0, h40477, hlam]
                            · linarith only [h39227, h40477, hlam]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [h39227, h40179, h40180, h40458, h40460, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p40461_1]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [h40177, hlam, p40461_0]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [hlam, p40461_0]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [h40180, hlam, p40461_0]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            rcases p40461_3 (m.d 0 1) (by simp) with h40484 | h40484
                            · linarith only [h33187, h40484, hlam]
                            · linarith only [h39227, h40484, hlam]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            rcases p40461_3 (m.d 0 1) (by simp) with h40487 | h40487
                            · linarith only [h40487, hlam, p40461_0]
                            · rcases p40461_3 (m.d 1 2) (by simp) with h40489 | h40489
                              · rcases p40461_3 (m.d 1 3) (by simp) with h40490 | h40490
                                · linarith only [h40180, h40490, hlam]
                                · linarith only [h33187, h40490, hlam]
                              · linarith only [h0, h40489, hlam]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [h40178, hlam, p40461_0]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [h33187, h39227, h40178, h40179, h40458, h40460, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p40461_1]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [hlam, p40461_0]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            rcases p40461_3 (m.d 0 1) (by simp) with h40497 | h40497
                            · linarith only [h36828, h40497, hlam]
                            · linarith only [h39227, h40497, hlam]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [h39227, hlam, p40461_0]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [h40179, hlam, p40461_0]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [h40454, hlam, p40461_0]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [h40455, hlam, p40461_0]
                          · have p40461_0 := h40461c.1
                            have p40461_1 := h40461c.2.1
                            have p40461_2 := h40461c.2.2.1
                            have p40461_3 := h40461c.2.2.2
                            linarith only [hlam, p40461_0]
                        · linarith only [h39231, h40176, h40460, hlam]
                      · linarith only [h33187, h39227, h40180, h40455, h40456, h40459, hc23, hc34, hlam, hphi]
                    · linarith only [h33187, h40175, h40180, h40458, hc23, hc34, hlam, hphi]
                · linarith only [h36828, h40176, h40455, hlam]
              · linarith only [h33187, h39227, h40175, h40179, h40454, hc03, hc25, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h39230, h40179, hlam]
        · linarith only [h0, h39229, h40178, hlam]
      · linarith only [h0, h39228, h40177, hlam]
    · linarith only [h33187, h39227, h39231, h40176, hlam]
  · linarith only [h33187, h39227, h40175, hlam]

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  rcases m.htr 0 3 4 (by decide) (by decide) with h39231 | h39231
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230 h39231

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h39230 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  linarith only [h0, h39227, h39230, hlam]

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  rcases m.htr 0 2 5 (by decide) (by decide) with h39230 | h39230
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229 h39230

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h39229 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  rcases m.htr 0 2 5 (by decide) (by decide) with h40516 | h40516
  · rcases m.htr 0 3 4 (by decide) (by decide) with h40517 | h40517
    · linarith only [h39228, h39229, h40517, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h40519 | h40519
      · rcases m.htr 0 4 5 (by decide) (by decide) with h40520 | h40520
        · rcases m.htr 1 2 3 (by decide) (by decide) with h40521 | h40521
          · rcases m.htr 1 2 4 (by decide) (by decide) with h40522 | h40522
            · rcases m.htr 1 2 5 (by decide) (by decide) with h40523 | h40523
              · rcases m.htr 1 3 4 (by decide) (by decide) with h40524 | h40524
                · rcases m.htr 1 3 5 (by decide) (by decide) with h40525 | h40525
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h40526 | h40526
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h40527 | h40527
                      · linarith only [h33187, h39227, h39228, h40517, h40523, h40527, hc02, hc25, hlam, hphi, ht0b, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h40529 | h40529
                        · linarith only [h39228, h39229, h40524, h40527, h40529, hc13, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h39228, h39229, h40519, h40521, h40524, h40527, h40529, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h36828, h40520, h40526, hlam]
                  · linarith only [h33187, h39228, h39229, h40519, h40522, h40525, hc01, hc14, hlam, hphi]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h40534 | h40534
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h40535 | h40535
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h40536 | h40536
                      · linarith only [h39228, h39229, h40522, h40524, h40536, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h40538 | h40538
                        · linarith only [h39228, h39229, h40522, h40538, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h39228, h39229, h40519, h40522, h40538, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h39228, h39229, h40522, h40535, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h33187, h39227, h39228, h40519, h40523, h40534, hc02, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h39229, h40522, h40523, hc02, hc25, hlam, hphi]
            · rcases m.htr 1 2 5 (by decide) (by decide) with h40544 | h40544
              · rcases m.htr 1 3 4 (by decide) (by decide) with h40545 | h40545
                · linarith only [h33187, h39227, h40517, h40521, h40522, h40544, h40545, hc24, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · rcases m.htr 1 3 5 (by decide) (by decide) with h40547 | h40547
                  · rcases m.htr 1 4 5 (by decide) (by decide) with h40548 | h40548
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h40549 | h40549
                      · linarith only [h0, h39228, h40522, h40545, h40549, hc13, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h40551 | h40551
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h40552 | h40552
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h40553 | h40553
                            · rcases h1bigk with h40554c | h40554c | h40554c | h40554c | h40554c | h40554c | h40554c | h40554c | h40554c | h40554c | h40554c | h40554c | h40554c | h40554c | h40554c | h40554c | h40554c | h40554c | h40554c | h40554c | h40554c | h40554c | h40554c | h40554c | h40554c
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [hlam, p40554_0]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [h0, hlam, p40554_0]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [h33187, hlam, p40554_0]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [h36828, hlam, p40554_0]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [h0, h40522, h40544, h40549, h40551, h40553, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p40554_1]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [h40522, h40549, hc01, hc34, hlam, hphi, ht12, ht23, p40554_1]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [hlam, p40554_0]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [h33187, h39227, h40522, h40544, h40549, h40551, h40553, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p40554_1]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [h40522, hlam, p40554_1]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                rcases p40554_3 (m.d 0 1) (by simp) with h40564 | h40564
                                · linarith only [h0, h40564, hlam]
                                · linarith only [h39227, h40564, hlam]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [h39227, h40521, h40522, h40544, h40549, h40551, h40553, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p40554_1]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [h40521, hlam, p40554_0]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [hlam, p40554_0]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [h40545, hlam, p40554_0]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                rcases p40554_3 (m.d 0 1) (by simp) with h40571 | h40571
                                · linarith only [h33187, h40571, hlam]
                                · linarith only [h39227, h40571, hlam]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                rcases p40554_3 (m.d 0 1) (by simp) with h40574 | h40574
                                · linarith only [h40574, hlam, p40554_0]
                                · rcases p40554_3 (m.d 1 2) (by simp) with h40576 | h40576
                                  · linarith only [h40522, h40576, hlam]
                                  · linarith only [h0, h40576, hlam]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [h0, h39228, h40522, h40549, hc23, hc34, hlam, hphi, p40554_1]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [h33187, h39227, h40522, h40544, h40549, h40551, h40553, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p40554_1]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [hlam, p40554_0]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                rcases p40554_3 (m.d 0 1) (by simp) with h40582 | h40582
                                · linarith only [h36828, h40582, hlam]
                                · linarith only [h39227, h40582, hlam]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [h39227, hlam, p40554_0]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [h40544, hlam, p40554_0]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [h40547, hlam, p40554_0]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [h40548, hlam, p40554_0]
                              · have p40554_0 := h40554c.1
                                have p40554_1 := h40554c.2.1
                                have p40554_2 := h40554c.2.2.1
                                have p40554_3 := h40554c.2.2.2
                                linarith only [hlam, p40554_0]
                            · linarith only [h39228, h39229, h40549, h40551, h40553, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h33187, h39227, h40521, h40522, h40548, h40552, hlam]
                        · linarith only [h0, h39228, h40519, h40522, h40549, h40551, hc23, hc34, hlam, hphi]
                    · linarith only [h36828, h40520, h40548, hlam]
                  · linarith only [h33187, h39227, h39228, h40519, h40544, h40547, hc02, hc25, hlam, hphi, ht0b, ht5b]
              · linarith only [h33187, h39227, h40516, h40521, h40544, hc02, hc15, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h39227, h39228, h40521, hc02, hc15, hlam, hphi, ht0b, ht5b]
        · linarith only [h0, h39227, h39229, h40520, hlam]
      · linarith only [h33187, h39227, h40519, hlam]
  · linarith only [h0, h39227, h40516, hlam]

set_option maxHeartbeats 17304000 in
set_option maxHeartbeats 17304000 in
theorem r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg33187 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg36828 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h39227 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h39228 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h33187 := hg33187
  have h36828 := hg36828
  rcases m.htr 0 2 4 (by decide) (by decide) with h39229 | h39229
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x0 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229
  · exact r1l7_11_12_14_25_L_I_L_I_L_I_H_I_s38_x0_x0_x1 m hb1 hb2 hb4 hb5 hg0 hg33187 hg36828 h39227 h39228 h39229

end R2N4
