import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_1S12
import Jsp000404.R1LeavesN7_1S13
import Jsp000404.R1LeavesN7_1S14

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg9966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9967 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9968 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h9970 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h9972 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
    (h9974 : (m.d 3 4 + m.lam ≤ m.d 1 3 ∧ m.d 3 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 3))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  have h9966 := hg9966
  rcases m.htr 1 3 5 (by decide) (by decide) with h11198 | h11198
  · rcases m.htr 1 4 5 (by decide) (by decide) with h11199 | h11199
    · rcases m.htr 2 3 4 (by decide) (by decide) with h11200 | h11200
      · rcases m.htr 2 3 5 (by decide) (by decide) with h11201 | h11201
        · rcases m.htr 2 4 5 (by decide) (by decide) with h11202 | h11202
          · rcases m.htr 3 4 5 (by decide) (by decide) with h11203 | h11203
            · rcases h0bigk with h11204c | h11204c | h11204c | h11204c | h11204c | h11204c | h11204c | h11204c | h11204c | h11204c | h11204c | h11204c | h11204c | h11204c | h11204c | h11204c | h11204c | h11204c | h11204c | h11204c | h11204c | h11204c | h11204c | h11204c | h11204c
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                linarith only [hlam, p11204_0]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                rcases p11204_3 (m.d 0 1) (by simp) with h11206 | h11206
                · rcases p11204_3 (m.d 0 2) (by simp) with h11207 | h11207
                  · linarith only [h0, h11207, hlam]
                  · rcases p11204_3 (m.d 0 3) (by simp) with h11209 | h11209
                    · linarith only [h1, h11209, hlam]
                    · linarith only [h11209, h4, hlam]
                · linarith only [h0, h11206, hlam]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                linarith only [h11198, h11203, h9965, h9974, hc01, hc45, hlam, hphi, ht0b, ht5b, p11204_1]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                linarith only [h11198, h11203, h9965, h9974, hc01, hc45, hlam, hphi, ht0b, ht5b, p11204_1]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                rcases p11204_3 (m.d 0 1) (by simp) with h11215 | h11215
                · rcases p11204_3 (m.d 0 2) (by simp) with h11216 | h11216
                  · linarith only [h0, h11216, hlam]
                  · rcases p11204_3 (m.d 0 3) (by simp) with h11218 | h11218
                    · linarith only [h1, h11218, hlam]
                    · linarith only [h11218, h9966, hlam]
                · linarith only [h11215, h3, hlam]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                linarith only [h0, hlam, p11204_0]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                linarith only [hlam, p11204_0]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                linarith only [h4, hlam, p11204_0]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                linarith only [h7821, hlam, p11204_1]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                linarith only [h9029, hlam, p11204_0]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                linarith only [h1, hlam, p11204_1]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                rcases p11204_3 (m.d 0 1) (by simp) with h11228 | h11228
                · rcases p11204_3 (m.d 0 2) (by simp) with h11229 | h11229
                  · linarith only [h11229, h4, hlam]
                  · rcases p11204_3 (m.d 0 3) (by simp) with h11231 | h11231
                    · rcases p11204_3 (m.d 0 4) (by simp) with h11232 | h11232
                      · linarith only [h11232, h9965, hlam]
                      · linarith only [h11232, h7821, hlam]
                    · linarith only [h11231, h4, hlam]
                · linarith only [h0, h11228, hlam]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                linarith only [hlam, p11204_0]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                linarith only [h11198, h11203, h9965, h9974, hc03, hc45, hlam, hphi, ht0b, ht5b, p11204_1]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                rcases p11204_3 (m.d 0 1) (by simp) with h11239 | h11239
                · rcases p11204_3 (m.d 0 2) (by simp) with h11240 | h11240
                  · linarith only [h11240, h4, hlam]
                  · rcases p11204_3 (m.d 0 3) (by simp) with h11242 | h11242
                    · rcases p11204_3 (m.d 0 4) (by simp) with h11243 | h11243
                      · linarith only [h11243, h9965, hlam]
                      · linarith only [h11243, h9967, hlam]
                    · linarith only [h11242, h9966, hlam]
                · linarith only [h11239, h3, hlam]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                linarith only [h2, hlam, p11204_0]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                rcases p11204_3 (m.d 0 1) (by simp) with h11249 | h11249
                · rcases p11204_3 (m.d 0 2) (by simp) with h11250 | h11250
                  · linarith only [h11250, h7821, hlam]
                  · rcases p11204_3 (m.d 0 3) (by simp) with h11252 | h11252
                    · rcases p11204_3 (m.d 0 4) (by simp) with h11253 | h11253
                      · rcases p11204_3 (m.d 0 5) (by simp) with h11254 | h11254
                        · linarith only [h11254, h9967, hlam]
                        · linarith only [h11254, h9029, hlam]
                      · linarith only [h11253, h7821, hlam]
                    · linarith only [h11252, h4, hlam]
                · linarith only [h0, h11249, hlam]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                linarith only [h9965, hlam, p11204_0]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                linarith only [hlam, p11204_0]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                rcases p11204_3 (m.d 0 1) (by simp) with h11262 | h11262
                · rcases p11204_3 (m.d 0 2) (by simp) with h11263 | h11263
                  · linarith only [h11263, h7821, hlam]
                  · rcases p11204_3 (m.d 0 3) (by simp) with h11265 | h11265
                    · rcases p11204_3 (m.d 0 4) (by simp) with h11266 | h11266
                      · rcases p11204_3 (m.d 0 5) (by simp) with h11267 | h11267
                        · linarith only [h11267, h9967, hlam]
                        · rcases h2bigk with h11269c | h11269c | h11269c | h11269c | h11269c | h11269c | h11269c | h11269c | h11269c | h11269c | h11269c | h11269c | h11269c | h11269c | h11269c | h11269c | h11269c | h11269c | h11269c | h11269c | h11269c | h11269c | h11269c | h11269c | h11269c
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            linarith only [hlam, p11269_0]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            linarith only [h9029, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11204_1, p11269_1]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            linarith only [h4, hlam, p11269_0]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            linarith only [h7821, hlam, p11269_0]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            linarith only [h9029, hlam, p11269_0]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            linarith only [h0, hlam, p11269_0]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            linarith only [hlam, p11269_0]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            linarith only [h9968, hlam, p11269_0]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            linarith only [h9970, hlam, p11269_0]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            linarith only [h9972, hlam, p11269_0]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            rcases p11269_3 (m.d 0 2) (by simp) with h11280 | h11280
                            · linarith only [h11280, hlam, p11269_0]
                            · rcases p11269_3 (m.d 1 2) (by simp) with h11282 | h11282
                              · linarith only [h11282, h9968, hlam]
                              · rcases p11269_3 (m.d 2 3) (by simp) with h11284 | h11284
                                · rcases p11269_3 (m.d 2 4) (by simp) with h11285 | h11285
                                  · linarith only [h11200, h11285, hlam]
                                  · linarith only [h11285, h7821, hlam]
                                · linarith only [h11284, hlam, p11269_0]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            rcases p11269_3 (m.d 0 2) (by simp) with h11289 | h11289
                            · linarith only [h11289, h4, hlam]
                            · linarith only [h0, h11289, hlam]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            linarith only [hlam, p11269_0]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            linarith only [h7821, hc02, hc23, hlam, hphi, p11269_1]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            linarith only [h0, h9029, hc12, hc23, hlam, hphi, p11269_1]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            rcases p11269_3 (m.d 0 2) (by simp) with h11295 | h11295
                            · linarith only [h11295, hlam, p11269_0]
                            · rcases p11269_3 (m.d 1 2) (by simp) with h11297 | h11297
                              · linarith only [h11297, h9970, hlam]
                              · rcases p11269_3 (m.d 2 3) (by simp) with h11299 | h11299
                                · rcases p11269_3 (m.d 2 4) (by simp) with h11300 | h11300
                                  · rcases p11269_3 (m.d 2 5) (by simp) with h11301 | h11301
                                    · linarith only [h11202, h11301, hlam]
                                    · linarith only [h11301, h9029, hlam]
                                  · linarith only [h11300, hlam, p11269_0]
                                · linarith only [h11299, h4, hlam]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            rcases p11269_3 (m.d 0 2) (by simp) with h11306 | h11306
                            · linarith only [h11306, h7821, hlam]
                            · linarith only [h0, h11306, hlam]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            linarith only [h11200, hlam, p11269_1]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            linarith only [hlam, p11269_0]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            linarith only [h0, h9029, hc12, hc24, hlam, hphi, p11269_1]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            rcases p11269_3 (m.d 0 2) (by simp) with h11312 | h11312
                            · linarith only [h11312, hlam, p11269_0]
                            · rcases p11269_3 (m.d 1 2) (by simp) with h11314 | h11314
                              · linarith only [h11314, h9972, hlam]
                              · rcases p11269_3 (m.d 2 3) (by simp) with h11316 | h11316
                                · rcases p11269_3 (m.d 2 4) (by simp) with h11317 | h11317
                                  · rcases p11269_3 (m.d 2 5) (by simp) with h11318 | h11318
                                    · rcases h3bigk with h11319c | h11319c | h11319c | h11319c | h11319c | h11319c | h11319c | h11319c | h11319c | h11319c | h11319c | h11319c | h11319c | h11319c | h11319c | h11319c | h11319c | h11319c | h11319c | h11319c | h11319c | h11319c | h11319c | h11319c | h11319c
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [hlam, p11319_0]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        rcases p11319_3 (m.d 0 3) (by simp) with h11321 | h11321
                                        · rcases p11319_3 (m.d 1 3) (by simp) with h11322 | h11322
                                          · linarith only [h1, h11322, hlam]
                                          · rcases p11319_3 (m.d 2 3) (by simp) with h11324 | h11324
                                            · rcases p11319_3 (m.d 3 4) (by simp) with h11325 | h11325
                                              · linarith only [h11325, h9965, hlam]
                                              · linarith only [h11325, h9974, hlam]
                                            · linarith only [h11324, h9968, hlam]
                                        · linarith only [h1, h11321, hlam]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [h4, hlam, p11319_1]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [h11198, h11203, h4, h9974, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11319_1]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [h11198, h9965, h9974, hlam, p11319_2]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [h1, hlam, p11319_0]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [hlam, p11319_0]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [h9968, hlam, p11319_1]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [h9974, hlam, p11319_0]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [h11203, h9965, h9974, hc03, hc45, hlam, hphi, ht0b, ht5b, p11319_1]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [h9965, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p11204_1, p11319_1]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        rcases p11319_3 (m.d 0 3) (by simp) with h11339 | h11339
                                        · linarith only [h11339, h4, hlam]
                                        · linarith only [h1, h11339, hlam]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [hlam, p11319_0]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [h11198, h11203, h9974, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11319_1]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [h11198, h4, h9965, h9974, hlam, p11319_2]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [h9965, hlam, p11319_0]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [h1, h11198, h11203, h9965, hc01, hc45, hlam, hphi, ht0b, ht5b, p11319_1]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [h11200, hlam, p11319_0]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [hlam, p11319_0]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        rcases p11319_3 (m.d 0 3) (by simp) with h11349 | h11349
                                        · rcases p11319_3 (m.d 1 3) (by simp) with h11350 | h11350
                                          · linarith only [h11350, h9974, hlam]
                                          · linarith only [h11198, h11350, hlam]
                                        · linarith only [h11349, h9966, hlam]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [h9966, hlam, p11319_0]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [h11198, hlam, p11319_0]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [h11201, hlam, p11319_0]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [h11203, hlam, p11319_0]
                                      · have p11319_0 := h11319c.1
                                        have p11319_1 := h11319c.2.1
                                        have p11319_2 := h11319c.2.2.1
                                        have p11319_3 := h11319c.2.2.2
                                        linarith only [hlam, p11319_0]
                                    · linarith only [h11318, hlam, p11269_0]
                                  · linarith only [h11317, h7821, hlam]
                                · linarith only [h11316, h4, hlam]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            rcases p11269_3 (m.d 0 2) (by simp) with h11362 | h11362
                            · linarith only [h11362, h9029, hlam]
                            · linarith only [h0, h11362, hlam]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            linarith only [h11201, hlam, p11269_1]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            linarith only [h11202, hlam, p11269_0]
                          · have p11269_0 := h11269c.1
                            have p11269_1 := h11269c.2.1
                            have p11269_2 := h11269c.2.2.1
                            have p11269_3 := h11269c.2.2.2
                            linarith only [hlam, p11269_0]
                      · linarith only [h11266, h9967, hlam]
                    · linarith only [h11265, h9966, hlam]
                · linarith only [h11262, h3, hlam]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                linarith only [h3, hlam, p11204_0]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                rcases p11204_3 (m.d 0 1) (by simp) with h11372 | h11372
                · rcases p11204_3 (m.d 0 2) (by simp) with h11373 | h11373
                  · linarith only [h11373, h9029, hlam]
                  · rcases p11204_3 (m.d 0 3) (by simp) with h11375 | h11375
                    · rcases p11204_3 (m.d 0 4) (by simp) with h11376 | h11376
                      · rcases p11204_3 (m.d 0 5) (by simp) with h11377 | h11377
                        · rcases h2bigk with h11378c | h11378c | h11378c | h11378c | h11378c | h11378c | h11378c | h11378c | h11378c | h11378c | h11378c | h11378c | h11378c | h11378c | h11378c | h11378c | h11378c | h11378c | h11378c | h11378c | h11378c | h11378c | h11378c | h11378c | h11378c
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            linarith only [hlam, p11378_0]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11204_1, p11378_1]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            linarith only [h4, hlam, p11378_0]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            linarith only [h7821, hlam, p11378_0]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            linarith only [h9029, hlam, p11378_0]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            linarith only [h0, hlam, p11378_0]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            linarith only [hlam, p11378_0]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            linarith only [h9968, hlam, p11378_0]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            linarith only [h9970, hlam, p11378_0]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            linarith only [h9972, hlam, p11378_0]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            rcases p11378_3 (m.d 0 2) (by simp) with h11389 | h11389
                            · linarith only [h11389, hlam, p11378_0]
                            · rcases p11378_3 (m.d 1 2) (by simp) with h11391 | h11391
                              · linarith only [h11391, h9968, hlam]
                              · rcases p11378_3 (m.d 2 3) (by simp) with h11393 | h11393
                                · rcases p11378_3 (m.d 2 4) (by simp) with h11394 | h11394
                                  · linarith only [h11200, h11394, hlam]
                                  · linarith only [h11394, h7821, hlam]
                                · linarith only [h11393, hlam, p11378_0]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            rcases p11378_3 (m.d 0 2) (by simp) with h11398 | h11398
                            · linarith only [h11398, h4, hlam]
                            · linarith only [h0, h11398, hlam]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            linarith only [hlam, p11378_0]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            linarith only [h7821, h9967, hc02, hc23, hlam, hphi, p11204_1, p11378_1]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            linarith only [h0, h9029, hc12, hc23, hlam, hphi, p11378_1]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            rcases p11378_3 (m.d 0 2) (by simp) with h11404 | h11404
                            · linarith only [h11404, hlam, p11378_0]
                            · rcases p11378_3 (m.d 1 2) (by simp) with h11406 | h11406
                              · linarith only [h11406, h9970, hlam]
                              · rcases p11378_3 (m.d 2 3) (by simp) with h11408 | h11408
                                · rcases p11378_3 (m.d 2 4) (by simp) with h11409 | h11409
                                  · rcases p11378_3 (m.d 2 5) (by simp) with h11410 | h11410
                                    · linarith only [h11202, h11410, hlam]
                                    · linarith only [h11410, h9029, hlam]
                                  · linarith only [h11409, hlam, p11378_0]
                                · linarith only [h11408, h4, hlam]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            rcases p11378_3 (m.d 0 2) (by simp) with h11415 | h11415
                            · linarith only [h11415, h7821, hlam]
                            · linarith only [h0, h11415, hlam]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            linarith only [h11200, hlam, p11378_1]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            linarith only [hlam, p11378_0]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            linarith only [h0, h9029, hc12, hc24, hlam, hphi, p11204_1, p11378_1]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            rcases p11378_3 (m.d 0 2) (by simp) with h11421 | h11421
                            · linarith only [h11421, hlam, p11378_0]
                            · rcases p11378_3 (m.d 1 2) (by simp) with h11423 | h11423
                              · linarith only [h11423, h9972, hlam]
                              · rcases p11378_3 (m.d 2 3) (by simp) with h11425 | h11425
                                · rcases p11378_3 (m.d 2 4) (by simp) with h11426 | h11426
                                  · rcases p11378_3 (m.d 2 5) (by simp) with h11427 | h11427
                                    · rcases h3bigk with h11428c | h11428c | h11428c | h11428c | h11428c | h11428c | h11428c | h11428c | h11428c | h11428c | h11428c | h11428c | h11428c | h11428c | h11428c | h11428c | h11428c | h11428c | h11428c | h11428c | h11428c | h11428c | h11428c | h11428c | h11428c
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [hlam, p11428_0]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        rcases p11428_3 (m.d 0 3) (by simp) with h11430 | h11430
                                        · rcases p11428_3 (m.d 1 3) (by simp) with h11431 | h11431
                                          · linarith only [h1, h11431, hlam]
                                          · rcases p11428_3 (m.d 2 3) (by simp) with h11433 | h11433
                                            · rcases p11428_3 (m.d 3 4) (by simp) with h11434 | h11434
                                              · linarith only [h11434, h9965, hlam]
                                              · linarith only [h11434, h9974, hlam]
                                            · linarith only [h11433, h9968, hlam]
                                        · linarith only [h1, h11430, hlam]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [h4, hlam, p11428_1]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [h11198, h11203, h4, h9974, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11428_1]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [h11198, h9965, h9974, hlam, p11428_2]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [h1, hlam, p11428_0]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [hlam, p11428_0]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [h9968, hlam, p11428_1]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [h9974, hlam, p11428_0]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [h11203, h9965, h9974, hc03, hc45, hlam, hphi, ht0b, ht5b, p11428_1]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [h9965, h9974, hc13, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p11428_1]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        rcases p11428_3 (m.d 0 3) (by simp) with h11448 | h11448
                                        · linarith only [h11448, h4, hlam]
                                        · linarith only [h1, h11448, hlam]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [hlam, p11428_0]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [h11198, h11203, h9974, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p11428_1]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [h11198, h4, h9965, h9974, hlam, p11428_2]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [h9965, hlam, p11428_0]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [h11198, h11203, h9965, hc03, hc45, hlam, hphi, ht0b, ht5b, p11428_1]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [h11200, hlam, p11428_0]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [hlam, p11428_0]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        rcases p11428_3 (m.d 0 3) (by simp) with h11458 | h11458
                                        · rcases p11428_3 (m.d 1 3) (by simp) with h11459 | h11459
                                          · linarith only [h11459, h9974, hlam]
                                          · linarith only [h11198, h11459, hlam]
                                        · linarith only [h11458, h9966, hlam]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [h9966, hlam, p11428_0]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [h11198, hlam, p11428_0]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [h11201, hlam, p11428_0]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [h11203, hlam, p11428_0]
                                      · have p11428_0 := h11428c.1
                                        have p11428_1 := h11428c.2.1
                                        have p11428_2 := h11428c.2.2.1
                                        have p11428_3 := h11428c.2.2.2
                                        linarith only [hlam, p11428_0]
                                    · linarith only [h11427, hlam, p11378_0]
                                  · linarith only [h11426, h7821, hlam]
                                · linarith only [h11425, h4, hlam]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            rcases p11378_3 (m.d 0 2) (by simp) with h11471 | h11471
                            · linarith only [h11471, h9029, hlam]
                            · linarith only [h0, h11471, hlam]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            linarith only [h11201, hlam, p11378_1]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            linarith only [h11202, hlam, p11378_0]
                          · have p11378_0 := h11378c.1
                            have p11378_1 := h11378c.2.1
                            have p11378_2 := h11378c.2.2.1
                            have p11378_3 := h11378c.2.2.2
                            linarith only [hlam, p11378_0]
                        · linarith only [h11377, h9029, hlam]
                      · linarith only [h11376, h7821, hlam]
                    · linarith only [h11375, h4, hlam]
                · linarith only [h0, h11372, hlam]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                linarith only [h9966, hlam, p11204_0]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                linarith only [h9967, hlam, p11204_1]
              · have p11204_0 := h11204c.1
                have p11204_1 := h11204c.2.1
                have p11204_2 := h11204c.2.2.1
                have p11204_3 := h11204c.2.2.2
                linarith only [hlam, p11204_0]
            · linarith only [h11198, h11203, h9967, h9974, hc04, hc35, hlam, hphi, ht0b, ht5b]
          · linarith only [h11198, h11199, h11202, h3, h7821, h9965, h9974, hc01, hc35, hlam, hphi, ht0b, ht5b]
        · linarith only [h11198, h11201, h4, h9965, h9974, hlam]
      · linarith only [h11200, h4, h9965, hlam]
    · linarith only [h11198, h11199, h9974, hlam]
  · rcases m.htr 1 4 5 (by decide) (by decide) with h11489 | h11489
    · rcases m.htr 2 3 4 (by decide) (by decide) with h11490 | h11490
      · rcases m.htr 2 3 5 (by decide) (by decide) with h11491 | h11491
        · rcases m.htr 2 4 5 (by decide) (by decide) with h11492 | h11492
          · rcases m.htr 3 4 5 (by decide) (by decide) with h11493 | h11493
            · rcases h0bigk with h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c | h11494c
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                linarith only [hlam, p11494_0]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                rcases p11494_3 (m.d 0 1) (by simp) with h11496 | h11496
                · rcases p11494_3 (m.d 0 2) (by simp) with h11497 | h11497
                  · linarith only [h0, h11497, hlam]
                  · rcases p11494_3 (m.d 0 3) (by simp) with h11499 | h11499
                    · linarith only [h1, h11499, hlam]
                    · linarith only [h11499, h4, hlam]
                · linarith only [h0, h11496, hlam]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                linarith only [h11198, h9966, h9968, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11494_1]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                rcases p11494_3 (m.d 0 1) (by simp) with h11504 | h11504
                · rcases p11494_3 (m.d 0 2) (by simp) with h11505 | h11505
                  · linarith only [h0, h11505, hlam]
                  · rcases p11494_3 (m.d 0 3) (by simp) with h11507 | h11507
                    · linarith only [h1, h11507, hlam]
                    · linarith only [h11507, h9965, hlam]
                · linarith only [h11504, h2, hlam]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                rcases p11494_3 (m.d 0 1) (by simp) with h11511 | h11511
                · rcases p11494_3 (m.d 0 2) (by simp) with h11512 | h11512
                  · linarith only [h0, h11512, hlam]
                  · rcases p11494_3 (m.d 0 3) (by simp) with h11514 | h11514
                    · linarith only [h1, h11514, hlam]
                    · linarith only [h11514, h9966, hlam]
                · linarith only [h11511, h3, hlam]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                linarith only [h0, hlam, p11494_0]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                linarith only [hlam, p11494_0]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                linarith only [h4, hlam, p11494_0]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                linarith only [h7821, hlam, p11494_1]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                linarith only [h9029, hlam, p11494_0]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                linarith only [h1, hlam, p11494_1]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                rcases p11494_3 (m.d 0 1) (by simp) with h11524 | h11524
                · rcases p11494_3 (m.d 0 2) (by simp) with h11525 | h11525
                  · linarith only [h11525, h4, hlam]
                  · rcases p11494_3 (m.d 0 3) (by simp) with h11527 | h11527
                    · rcases p11494_3 (m.d 0 4) (by simp) with h11528 | h11528
                      · linarith only [h11528, h9965, hlam]
                      · linarith only [h11528, h7821, hlam]
                    · linarith only [h11527, h4, hlam]
                · linarith only [h0, h11524, hlam]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                linarith only [hlam, p11494_0]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                linarith only [h11198, h4, h9966, h9967, h9968, hc12, hc23, hlam, hphi, p11494_1]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                linarith only [h11198, h4, h9966, h9968, hc12, hc23, hlam, hphi, p11494_1]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                linarith only [h2, hlam, p11494_0]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                rcases p11494_3 (m.d 0 1) (by simp) with h11537 | h11537
                · rcases p11494_3 (m.d 0 2) (by simp) with h11538 | h11538
                  · linarith only [h11538, h7821, hlam]
                  · rcases p11494_3 (m.d 0 3) (by simp) with h11540 | h11540
                    · rcases p11494_3 (m.d 0 4) (by simp) with h11541 | h11541
                      · rcases p11494_3 (m.d 0 5) (by simp) with h11542 | h11542
                        · linarith only [h11542, h9967, hlam]
                        · linarith only [h11542, h9029, hlam]
                      · linarith only [h11541, h7821, hlam]
                    · linarith only [h11540, h4, hlam]
                · linarith only [h0, h11537, hlam]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                linarith only [h9965, hlam, p11494_0]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                linarith only [hlam, p11494_0]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                linarith only [h11198, h7821, h9966, h9968, hc12, hc24, hlam, hphi, p11494_1]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                linarith only [h3, hlam, p11494_0]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                rcases p11494_3 (m.d 0 1) (by simp) with h11552 | h11552
                · rcases p11494_3 (m.d 0 2) (by simp) with h11553 | h11553
                  · linarith only [h11553, h9029, hlam]
                  · rcases p11494_3 (m.d 0 3) (by simp) with h11555 | h11555
                    · rcases p11494_3 (m.d 0 4) (by simp) with h11556 | h11556
                      · rcases p11494_3 (m.d 0 5) (by simp) with h11557 | h11557
                        · rcases h2bigk with h11558c | h11558c | h11558c | h11558c | h11558c | h11558c | h11558c | h11558c | h11558c | h11558c | h11558c | h11558c | h11558c | h11558c | h11558c | h11558c | h11558c | h11558c | h11558c | h11558c | h11558c | h11558c | h11558c | h11558c | h11558c
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            linarith only [hlam, p11558_0]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            linarith only [hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p11494_1, p11558_1]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            linarith only [h4, hlam, p11558_0]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            linarith only [h7821, hlam, p11558_0]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            linarith only [h9029, hlam, p11558_0]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            linarith only [h0, hlam, p11558_0]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            linarith only [hlam, p11558_0]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            linarith only [h9968, hlam, p11558_0]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            linarith only [h9970, hlam, p11558_0]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            linarith only [h9972, hlam, p11558_0]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            rcases p11558_3 (m.d 0 2) (by simp) with h11569 | h11569
                            · linarith only [h11569, hlam, p11558_0]
                            · rcases p11558_3 (m.d 1 2) (by simp) with h11571 | h11571
                              · linarith only [h11571, h9968, hlam]
                              · rcases p11558_3 (m.d 2 3) (by simp) with h11573 | h11573
                                · rcases p11558_3 (m.d 2 4) (by simp) with h11574 | h11574
                                  · linarith only [h11490, h11574, hlam]
                                  · linarith only [h11574, h7821, hlam]
                                · linarith only [h11573, hlam, p11558_0]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            rcases p11558_3 (m.d 0 2) (by simp) with h11578 | h11578
                            · linarith only [h11578, h4, hlam]
                            · linarith only [h0, h11578, hlam]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            linarith only [hlam, p11558_0]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            linarith only [h7821, hc02, hc23, hlam, hphi, p11558_1]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            linarith only [h0, h9029, hc12, hc23, hlam, hphi, p11558_1]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            rcases p11558_3 (m.d 0 2) (by simp) with h11584 | h11584
                            · linarith only [h11584, hlam, p11558_0]
                            · rcases p11558_3 (m.d 1 2) (by simp) with h11586 | h11586
                              · linarith only [h11586, h9970, hlam]
                              · rcases p11558_3 (m.d 2 3) (by simp) with h11588 | h11588
                                · rcases p11558_3 (m.d 2 4) (by simp) with h11589 | h11589
                                  · rcases p11558_3 (m.d 2 5) (by simp) with h11590 | h11590
                                    · linarith only [h11492, h11590, hlam]
                                    · linarith only [h11590, h9029, hlam]
                                  · linarith only [h11589, hlam, p11558_0]
                                · linarith only [h11588, h4, hlam]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            rcases p11558_3 (m.d 0 2) (by simp) with h11595 | h11595
                            · linarith only [h11595, h7821, hlam]
                            · linarith only [h0, h11595, hlam]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            linarith only [h11490, hlam, p11558_1]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            linarith only [hlam, p11558_0]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            linarith only [h0, h9029, hc12, hc24, hlam, hphi, p11494_1, p11558_1]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            rcases p11558_3 (m.d 0 2) (by simp) with h11601 | h11601
                            · linarith only [h11601, hlam, p11558_0]
                            · rcases p11558_3 (m.d 1 2) (by simp) with h11603 | h11603
                              · linarith only [h11603, h9972, hlam]
                              · rcases p11558_3 (m.d 2 3) (by simp) with h11605 | h11605
                                · rcases p11558_3 (m.d 2 4) (by simp) with h11606 | h11606
                                  · rcases p11558_3 (m.d 2 5) (by simp) with h11607 | h11607
                                    · rcases h3bigk with h11608c | h11608c | h11608c | h11608c | h11608c | h11608c | h11608c | h11608c | h11608c | h11608c | h11608c | h11608c | h11608c | h11608c | h11608c | h11608c | h11608c | h11608c | h11608c | h11608c | h11608c | h11608c | h11608c | h11608c | h11608c
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [hlam, p11608_0]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        rcases p11608_3 (m.d 0 3) (by simp) with h11610 | h11610
                                        · rcases p11608_3 (m.d 1 3) (by simp) with h11611 | h11611
                                          · linarith only [h1, h11611, hlam]
                                          · rcases p11608_3 (m.d 2 3) (by simp) with h11613 | h11613
                                            · rcases p11608_3 (m.d 3 4) (by simp) with h11614 | h11614
                                              · linarith only [h11614, h9965, hlam]
                                              · linarith only [h11614, h9974, hlam]
                                            · linarith only [h11613, h9968, hlam]
                                        · linarith only [h1, h11610, hlam]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [h4, hlam, p11608_1]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [h11198, h11493, h4, h9968, hc12, hc23, hlam, hphi, p11608_1]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [h11198, h4, h9968, hc12, hc23, hlam, hphi, p11608_1]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [h1, hlam, p11608_0]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [hlam, p11608_0]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [h9968, hlam, p11608_1]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [h9974, hlam, p11608_0]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [h11198, hlam, p11608_0]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [h11198, h11493, h9965, h9968, hc12, hc23, hlam, hphi, p11608_1]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        rcases p11608_3 (m.d 0 3) (by simp) with h11628 | h11628
                                        · linarith only [h11628, h4, hlam]
                                        · linarith only [h1, h11628, hlam]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [hlam, p11608_0]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [h9968, h9974, hc12, hc23, hlam, hphi, p11608_1]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [h11198, h9968, hc12, hc23, hlam, hphi, p11608_1]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [h9965, hlam, p11608_0]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [h4, h9965, h9968, hc12, hc23, hlam, hphi, p11608_1]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [h11490, hlam, p11608_0]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [hlam, p11608_0]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [h11198, h4, h9965, h9968, hc12, hc23, hlam, hphi, p11608_1]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [h9966, hlam, p11608_0]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [h4, h9966, h9968, hc12, hc23, hlam, hphi, p11608_1]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [h11491, hlam, p11608_0]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [h11493, hlam, p11608_0]
                                      · have p11608_0 := h11608c.1
                                        have p11608_1 := h11608c.2.1
                                        have p11608_2 := h11608c.2.2.1
                                        have p11608_3 := h11608c.2.2.2
                                        linarith only [hlam, p11608_0]
                                    · linarith only [h11607, hlam, p11558_0]
                                  · linarith only [h11606, h7821, hlam]
                                · linarith only [h11605, h4, hlam]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            rcases p11558_3 (m.d 0 2) (by simp) with h11647 | h11647
                            · linarith only [h11647, h9029, hlam]
                            · linarith only [h0, h11647, hlam]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            linarith only [h11491, hlam, p11558_1]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            linarith only [h11492, hlam, p11558_0]
                          · have p11558_0 := h11558c.1
                            have p11558_1 := h11558c.2.1
                            have p11558_2 := h11558c.2.2.1
                            have p11558_3 := h11558c.2.2.2
                            linarith only [hlam, p11558_0]
                        · linarith only [h11557, h9029, hlam]
                      · linarith only [h11556, h7821, hlam]
                    · linarith only [h11555, h4, hlam]
                · linarith only [h0, h11552, hlam]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                linarith only [h9966, hlam, p11494_0]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                linarith only [h9967, hlam, p11494_1]
              · have p11494_0 := h11494c.1
                have p11494_1 := h11494c.2.1
                have p11494_2 := h11494c.2.2.1
                have p11494_3 := h11494c.2.2.2
                linarith only [hlam, p11494_0]
            · linarith only [h11489, h11493, h9974, hlam]
          · linarith only [h0, h11489, h11492, h4, h7821, h9965, h9974, hc12, hc23, hlam, hphi]
        · linarith only [h11491, h4, h9966, hlam]
      · linarith only [h11490, h4, h9965, hlam]
    · rcases m.htr 2 3 4 (by decide) (by decide) with h11664 | h11664
      · rcases m.htr 2 3 5 (by decide) (by decide) with h11665 | h11665
        · rcases m.htr 2 4 5 (by decide) (by decide) with h11666 | h11666
          · rcases m.htr 3 4 5 (by decide) (by decide) with h11667 | h11667
            · linarith only [h11489, h11667, h4, h9965, h9968, h9974, hc12, hc23, hlam, hphi]
            · linarith only [h11667, h7821, h9967, h9968, h9974, hc12, hc24, hlam, hphi]
          · linarith only [h0, h11666, h4, h7821, h9965, h9967, hc12, hc23, hlam, hphi]
        · linarith only [h11665, h4, h9966, hlam]
      · linarith only [h11664, h4, h9965, hlam]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg9966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9967 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9968 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h9970 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h9972 : (m.d 2 5 + m.lam ≤ m.d 1 2 ∧ m.d 2 5 < m.d 1 5 ∧ m.d 1 5 < m.d 1 2))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  have h9966 := hg9966
  rcases m.htr 1 3 4 (by decide) (by decide) with h9974 | h9974
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h9968 h9970 h9972 h9974
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h9968 h9970 h9972 h9974

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg9966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9967 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9968 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h9970 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  have h9966 := hg9966
  rcases m.htr 1 2 5 (by decide) (by decide) with h9972 | h9972
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h9968 h9970 h9972
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h9968 h9970 h9972

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg9966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9967 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
    (h9968 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  have h9966 := hg9966
  rcases m.htr 1 2 4 (by decide) (by decide) with h9970 | h9970
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h9968 h9970
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h9968 h9970

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg9966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9967 : (m.d 0 4 + m.lam ≤ m.d 4 5 ∧ m.d 0 4 < m.d 0 5 ∧ m.d 0 5 < m.d 4 5))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  have h9966 := hg9966
  rcases m.htr 1 2 3 (by decide) (by decide) with h9968 | h9968
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x0 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h9968
  · exact r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x0_x1 m hb0 hb2 hb3 hb5 hg0 hg1 hg2 hg3 hg4 hg7821 hg9029 hg9965 hg9966 h9967 h9968

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg9966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9967 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11673 : (m.d 1 2 + m.lam ≤ m.d 2 3 ∧ m.d 1 2 < m.d 1 3 ∧ m.d 1 3 < m.d 2 3))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  have h9966 := hg9966
  linarith only [h0, h11673, h4, hlam]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg9966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9967 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11673 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h11675 : (m.d 1 2 + m.lam ≤ m.d 2 4 ∧ m.d 1 2 < m.d 1 4 ∧ m.d 1 4 < m.d 2 4))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  have h9966 := hg9966
  linarith only [h0, h11675, h7821, hlam]

set_option maxHeartbeats 5222000 in
set_option maxHeartbeats 5222000 in
theorem r1l7_10_12_13_25_L_I_L_I_L_I_H_I_s15_x1_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg7821 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (hg9029 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
    (hg9965 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (hg9966 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h9967 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
    (h11673 : (m.d 2 3 + m.lam ≤ m.d 1 2 ∧ m.d 2 3 < m.d 1 3 ∧ m.d 1 3 < m.d 1 2))
    (h11675 : (m.d 2 4 + m.lam ≤ m.d 1 2 ∧ m.d 2 4 < m.d 1 4 ∧ m.d 1 4 < m.d 1 2))
    (h11677 : (m.d 1 2 + m.lam ≤ m.d 2 5 ∧ m.d 1 2 < m.d 1 5 ∧ m.d 1 5 < m.d 2 5))
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
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h7821 := hg7821
  have h9029 := hg9029
  have h9965 := hg9965
  have h9966 := hg9966
  linarith only [h0, h11677, h9029, hlam]

end R2N4
