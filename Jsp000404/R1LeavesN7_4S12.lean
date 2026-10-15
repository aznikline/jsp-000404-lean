import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S11

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 5858000 in
set_option maxHeartbeats 5858000 in
theorem r1l7_11_23_L_I_H_I_s10_x0_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg6364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h7232 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7233 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h7234 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h6364 := hg6364
  rcases m.htr 1 2 3 (by decide) (by decide) with h8201 | h8201
  · linarith only [h0, h4, h8201, hlam]
  · rcases m.htr 1 2 4 (by decide) (by decide) with h8203 | h8203
    · linarith only [h0, h6364, h8203, hlam]
    · rcases m.htr 1 2 5 (by decide) (by decide) with h8205 | h8205
      · rcases m.htr 1 3 4 (by decide) (by decide) with h8206 | h8206
        · rcases m.htr 1 3 5 (by decide) (by decide) with h8207 | h8207
          · rcases m.htr 1 4 5 (by decide) (by decide) with h8208 | h8208
            · linarith only [h0, h2, h6364, h7234, h8205, h8208, hc01, hc25, hlam, hphi, ht0b, ht5b]
            · linarith only [h8203, h8205, h8208, hlam]
          · linarith only [h8201, h8205, h8207, hlam]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h8212 | h8212
          · rcases m.htr 1 4 5 (by decide) (by decide) with h8213 | h8213
            · linarith only [h7232, h7234, h8206, h8212, h8213, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
            · linarith only [h8203, h8205, h8213, hlam]
          · linarith only [h8201, h8205, h8212, hlam]
      · rcases m.htr 1 3 4 (by decide) (by decide) with h8217 | h8217
        · rcases m.htr 1 3 5 (by decide) (by decide) with h8218 | h8218
          · rcases m.htr 1 4 5 (by decide) (by decide) with h8219 | h8219
            · linarith only [h2, h7234, h8219, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h8221 | h8221
              · rcases m.htr 2 3 5 (by decide) (by decide) with h8222 | h8222
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8223 | h8223
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8224 | h8224
                    · linarith only [h2, h7234, h8217, h8224, hlam]
                    · rcases h1bigk with h8226c | h8226c | h8226c | h8226c | h8226c | h8226c | h8226c | h8226c | h8226c | h8226c | h8226c | h8226c | h8226c | h8226c | h8226c | h8226c | h8226c | h8226c | h8226c | h8226c | h8226c | h8226c | h8226c | h8226c | h8226c
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        linarith only [hlam, p8226_0]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        rcases p8226_3 (m.d 0 1) (by simp) with h8228 | h8228
                        · rcases p8226_3 (m.d 1 2) (by simp) with h8229 | h8229
                          · linarith only [h8229, hlam, p8226_0]
                          · rcases p8226_3 (m.d 1 3) (by simp) with h8231 | h8231
                            · linarith only [h1, h8231, hlam]
                            · linarith only [h8201, h8231, hlam]
                        · linarith only [h8228, hlam, p8226_0]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        rcases p8226_3 (m.d 0 1) (by simp) with h8235 | h8235
                        · rcases p8226_3 (m.d 1 2) (by simp) with h8236 | h8236
                          · linarith only [h0, h8236, hlam]
                          · rcases p8226_3 (m.d 1 3) (by simp) with h8238 | h8238
                            · linarith only [h8238, hlam, p8226_0]
                            · rcases p8226_3 (m.d 1 4) (by simp) with h8240 | h8240
                              · linarith only [h2, h8240, hlam]
                              · rcases p8226_3 (m.d 1 5) (by simp) with h8242 | h8242
                                · linarith only [h3, h8242, hlam]
                                · rcases h3bigk with h8244c | h8244c | h8244c | h8244c | h8244c | h8244c | h8244c | h8244c | h8244c | h8244c | h8244c | h8244c | h8244c | h8244c | h8244c | h8244c | h8244c | h8244c | h8244c | h8244c | h8244c | h8244c | h8244c | h8244c | h8244c
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [hlam, p8244_0]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [h1, h8218, h8224, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8244_1]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [h4, hlam, p8244_1]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    rcases p8244_3 (m.d 0 3) (by simp) with h8248 | h8248
                                    · rcases p8244_3 (m.d 1 3) (by simp) with h8249 | h8249
                                      · linarith only [h1, h8249, hlam]
                                      · linarith only [h8217, h8249, hlam]
                                    · linarith only [h8248, hlam, p8244_0]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    rcases p8244_3 (m.d 0 3) (by simp) with h8253 | h8253
                                    · rcases p8244_3 (m.d 1 3) (by simp) with h8254 | h8254
                                      · linarith only [h1, h8254, hlam]
                                      · linarith only [h8218, h8254, hlam]
                                    · linarith only [h8253, hlam, p8244_0]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [h1, hlam, p8244_0]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [hlam, p8244_0]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [h8201, hlam, p8244_1]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8226_1, p8244_1]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [hc01, hc35, hlam, hphi, ht0b, ht5b, p8226_1, p8244_1]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [h0, h4, hc12, hc23, hlam, hphi, p8244_1]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [h8201, hc12, hc23, hlam, hphi, p8244_1]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [hlam, p8244_0]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    rcases p8244_3 (m.d 0 3) (by simp) with h8266 | h8266
                                    · linarith only [h4, h8266, hlam]
                                    · linarith only [h7232, h8266, hlam]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    rcases p8244_3 (m.d 0 3) (by simp) with h8269 | h8269
                                    · linarith only [h4, h8269, hlam]
                                    · linarith only [h7233, h8269, hlam]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [h7232, hlam, p8244_0]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [h8217, hlam, p8244_0]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [h8221, hlam, p8244_0]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [hlam, p8244_0]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [h8224, hlam, p8244_1]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [h7233, hlam, p8244_0]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [h8218, hlam, p8244_0]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [h8222, hlam, p8244_0]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [h1, h8218, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p8244_1]
                                  · have p8244_0 := h8244c.1
                                    have p8244_1 := h8244c.2.1
                                    have p8244_2 := h8244c.2.2.1
                                    have p8244_3 := h8244c.2.2.2
                                    linarith only [hlam, p8244_0]
                        · linarith only [h8235, hlam, p8226_0]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        rcases p8226_3 (m.d 0 1) (by simp) with h8283 | h8283
                        · rcases p8226_3 (m.d 1 2) (by simp) with h8284 | h8284
                          · linarith only [h0, h8284, hlam]
                          · rcases p8226_3 (m.d 1 3) (by simp) with h8286 | h8286
                            · linarith only [h1, h8286, hlam]
                            · linarith only [h8217, h8286, hlam]
                        · linarith only [h8283, hlam, p8226_0]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        rcases p8226_3 (m.d 0 1) (by simp) with h8290 | h8290
                        · rcases p8226_3 (m.d 1 2) (by simp) with h8291 | h8291
                          · linarith only [h0, h8291, hlam]
                          · rcases p8226_3 (m.d 1 3) (by simp) with h8293 | h8293
                            · linarith only [h1, h8293, hlam]
                            · linarith only [h8218, h8293, hlam]
                        · linarith only [h8290, hlam, p8226_0]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        linarith only [h0, hlam, p8226_0]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        linarith only [hlam, p8226_0]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        linarith only [h8201, hlam, p8226_0]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        linarith only [h8203, hlam, p8226_0]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        linarith only [h8205, hlam, p8226_0]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        linarith only [h1, hlam, p8226_0]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        rcases p8226_3 (m.d 0 1) (by simp) with h8303 | h8303
                        · rcases p8226_3 (m.d 1 2) (by simp) with h8304 | h8304
                          · linarith only [h8201, h8304, hlam]
                          · rcases p8226_3 (m.d 1 3) (by simp) with h8306 | h8306
                            · rcases p8226_3 (m.d 1 4) (by simp) with h8307 | h8307
                              · linarith only [h8217, h8307, hlam]
                              · linarith only [h8203, h8307, hlam]
                            · linarith only [h8201, h8306, hlam]
                        · linarith only [h0, h8303, hlam]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        linarith only [hlam, p8226_0]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        rcases p8226_3 (m.d 0 1) (by simp) with h8313 | h8313
                        · rcases p8226_3 (m.d 1 2) (by simp) with h8314 | h8314
                          · linarith only [h8201, h8314, hlam]
                          · rcases p8226_3 (m.d 1 3) (by simp) with h8316 | h8316
                            · rcases p8226_3 (m.d 1 4) (by simp) with h8317 | h8317
                              · linarith only [h8217, h8317, hlam]
                              · rcases p8226_3 (m.d 1 5) (by simp) with h8319 | h8319
                                · linarith only [h8218, h8319, hlam]
                                · linarith only [h8219, h8319, hlam]
                            · linarith only [h8217, h8316, hlam]
                        · linarith only [h2, h8313, hlam]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        rcases p8226_3 (m.d 0 1) (by simp) with h8324 | h8324
                        · rcases p8226_3 (m.d 1 2) (by simp) with h8325 | h8325
                          · linarith only [h8201, h8325, hlam]
                          · rcases p8226_3 (m.d 1 3) (by simp) with h8327 | h8327
                            · rcases p8226_3 (m.d 1 4) (by simp) with h8328 | h8328
                              · linarith only [h8217, h8328, hlam]
                              · rcases p8226_3 (m.d 1 5) (by simp) with h8330 | h8330
                                · linarith only [h8218, h8330, hlam]
                                · rcases h3bigk with h8332c | h8332c | h8332c | h8332c | h8332c | h8332c | h8332c | h8332c | h8332c | h8332c | h8332c | h8332c | h8332c | h8332c | h8332c | h8332c | h8332c | h8332c | h8332c | h8332c | h8332c | h8332c | h8332c | h8332c | h8332c
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [hlam, p8332_0]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [h4, h8203, h8219, hc12, hc23, hlam, hphi, p8226_1, p8332_1]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [h4, hlam, p8332_1]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    rcases p8332_3 (m.d 0 3) (by simp) with h8336 | h8336
                                    · rcases p8332_3 (m.d 1 3) (by simp) with h8337 | h8337
                                      · linarith only [h1, h8337, hlam]
                                      · linarith only [h8217, h8337, hlam]
                                    · linarith only [h8336, hlam, p8332_0]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    rcases p8332_3 (m.d 0 3) (by simp) with h8341 | h8341
                                    · rcases p8332_3 (m.d 1 3) (by simp) with h8342 | h8342
                                      · linarith only [h1, h8342, hlam]
                                      · linarith only [h8218, h8342, hlam]
                                    · linarith only [h8341, hlam, p8332_0]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [h1, hlam, p8332_0]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [hlam, p8332_0]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [h8201, hlam, p8332_1]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8332_1]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p8332_1]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [h1, h8203, h8219, hc12, hc23, hlam, hphi, p8226_1, p8332_1]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [h8203, h8219, hc12, hc23, hlam, hphi, p8226_1, p8332_1]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [hlam, p8332_0]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    rcases p8332_3 (m.d 0 3) (by simp) with h8354 | h8354
                                    · linarith only [h4, h8354, hlam]
                                    · linarith only [h7232, h8354, hlam]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    rcases p8332_3 (m.d 0 3) (by simp) with h8357 | h8357
                                    · linarith only [h4, h8357, hlam]
                                    · linarith only [h7233, h8357, hlam]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [h7232, hlam, p8332_0]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [h8217, hlam, p8332_0]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [h8221, hlam, p8332_0]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [hlam, p8332_0]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [h8224, hlam, p8332_1]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [h7233, hlam, p8332_0]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [h8218, hlam, p8332_0]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [h8222, hlam, p8332_0]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [h7233, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p8332_1]
                                  · have p8332_0 := h8332c.1
                                    have p8332_1 := h8332c.2.1
                                    have p8332_2 := h8332c.2.2.1
                                    have p8332_3 := h8332c.2.2.2
                                    linarith only [hlam, p8332_0]
                            · linarith only [h8218, h8327, hlam]
                        · linarith only [h3, h8324, hlam]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        linarith only [h2, hlam, p8226_0]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        linarith only [h2, h7234, h8221, h8223, hc12, hc23, hlam, hphi, p8226_1]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        linarith only [h8217, hlam, p8226_0]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        linarith only [hlam, p8226_0]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        linarith only [h8219, hlam, p8226_1]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        linarith only [h3, hlam, p8226_0]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        linarith only [h3, h7234, h8221, h8223, hc12, hc23, hlam, hphi, p8226_1]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        linarith only [h8218, hlam, p8226_0]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        linarith only [h3, h7234, h8203, h8221, h8223, hc12, hc23, hlam, hphi, p8226_1]
                      · have p8226_0 := h8226c.1
                        have p8226_1 := h8226c.2.1
                        have p8226_2 := h8226c.2.2.1
                        have p8226_3 := h8226c.2.2.2
                        linarith only [hlam, p8226_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8382 | h8382
                    · linarith only [h0, h6364, h8223, h8382, hc12, hc34, hlam, hphi, ht23]
                    · rcases h1bigk with h8384c | h8384c | h8384c | h8384c | h8384c | h8384c | h8384c | h8384c | h8384c | h8384c | h8384c | h8384c | h8384c | h8384c | h8384c | h8384c | h8384c | h8384c | h8384c | h8384c | h8384c | h8384c | h8384c | h8384c | h8384c
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        linarith only [hlam, p8384_0]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        rcases p8384_3 (m.d 0 1) (by simp) with h8386 | h8386
                        · rcases p8384_3 (m.d 1 2) (by simp) with h8387 | h8387
                          · linarith only [h8387, hlam, p8384_0]
                          · rcases p8384_3 (m.d 1 3) (by simp) with h8389 | h8389
                            · linarith only [h1, h8389, hlam]
                            · linarith only [h8201, h8389, hlam]
                        · linarith only [h8386, hlam, p8384_0]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        rcases p8384_3 (m.d 0 1) (by simp) with h8393 | h8393
                        · rcases p8384_3 (m.d 1 2) (by simp) with h8394 | h8394
                          · linarith only [h0, h8394, hlam]
                          · rcases p8384_3 (m.d 1 3) (by simp) with h8396 | h8396
                            · linarith only [h8396, hlam, p8384_0]
                            · rcases p8384_3 (m.d 1 4) (by simp) with h8398 | h8398
                              · linarith only [h2, h8398, hlam]
                              · rcases p8384_3 (m.d 1 5) (by simp) with h8400 | h8400
                                · linarith only [h3, h8400, hlam]
                                · rcases h3bigk with h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c | h8402c
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [hlam, p8402_0]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [h4, h8218, h8382, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8402_1]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [h4, hlam, p8402_1]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    rcases p8402_3 (m.d 0 3) (by simp) with h8406 | h8406
                                    · rcases p8402_3 (m.d 1 3) (by simp) with h8407 | h8407
                                      · linarith only [h1, h8407, hlam]
                                      · linarith only [h8217, h8407, hlam]
                                    · linarith only [h8406, hlam, p8402_0]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    rcases p8402_3 (m.d 0 3) (by simp) with h8411 | h8411
                                    · rcases p8402_3 (m.d 1 3) (by simp) with h8412 | h8412
                                      · linarith only [h1, h8412, hlam]
                                      · linarith only [h8218, h8412, hlam]
                                    · linarith only [h8411, hlam, p8402_0]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [h1, hlam, p8402_0]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [hlam, p8402_0]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [h8201, hlam, p8402_1]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8384_1, p8402_1]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [h8382, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8384_1, p8402_1]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [h0, h4, hc12, hc23, hlam, hphi, p8402_1]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [h8201, hc12, hc23, hlam, hphi, p8402_1]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [hlam, p8402_0]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    rcases p8402_3 (m.d 0 3) (by simp) with h8424 | h8424
                                    · linarith only [h4, h8424, hlam]
                                    · linarith only [h7232, h8424, hlam]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    rcases p8402_3 (m.d 0 3) (by simp) with h8427 | h8427
                                    · linarith only [h4, h8427, hlam]
                                    · linarith only [h7233, h8427, hlam]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [h7232, hlam, p8402_0]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [h8217, hlam, p8402_0]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [h8221, hlam, p8402_0]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [hlam, p8402_0]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [h8382, hlam, p8402_1]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [h7233, hlam, p8402_0]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [h8218, hlam, p8402_0]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [h8222, hlam, p8402_0]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [h1, h8218, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p8402_1]
                                  · have p8402_0 := h8402c.1
                                    have p8402_1 := h8402c.2.1
                                    have p8402_2 := h8402c.2.2.1
                                    have p8402_3 := h8402c.2.2.2
                                    linarith only [hlam, p8402_0]
                        · linarith only [h8393, hlam, p8384_0]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        rcases p8384_3 (m.d 0 1) (by simp) with h8441 | h8441
                        · rcases p8384_3 (m.d 1 2) (by simp) with h8442 | h8442
                          · linarith only [h0, h8442, hlam]
                          · rcases p8384_3 (m.d 1 3) (by simp) with h8444 | h8444
                            · linarith only [h1, h8444, hlam]
                            · linarith only [h8217, h8444, hlam]
                        · linarith only [h8441, hlam, p8384_0]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        rcases p8384_3 (m.d 0 1) (by simp) with h8448 | h8448
                        · rcases p8384_3 (m.d 1 2) (by simp) with h8449 | h8449
                          · linarith only [h0, h8449, hlam]
                          · rcases p8384_3 (m.d 1 3) (by simp) with h8451 | h8451
                            · linarith only [h1, h8451, hlam]
                            · linarith only [h8218, h8451, hlam]
                        · linarith only [h8448, hlam, p8384_0]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        linarith only [h0, hlam, p8384_0]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        linarith only [hlam, p8384_0]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        linarith only [h8201, hlam, p8384_0]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        linarith only [h8203, hlam, p8384_0]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        linarith only [h8205, hlam, p8384_0]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        linarith only [h1, hlam, p8384_0]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        rcases p8384_3 (m.d 0 1) (by simp) with h8461 | h8461
                        · rcases p8384_3 (m.d 1 2) (by simp) with h8462 | h8462
                          · linarith only [h8201, h8462, hlam]
                          · rcases p8384_3 (m.d 1 3) (by simp) with h8464 | h8464
                            · rcases p8384_3 (m.d 1 4) (by simp) with h8465 | h8465
                              · linarith only [h8217, h8465, hlam]
                              · linarith only [h8203, h8465, hlam]
                            · linarith only [h8201, h8464, hlam]
                        · linarith only [h0, h8461, hlam]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        linarith only [hlam, p8384_0]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        rcases p8384_3 (m.d 0 1) (by simp) with h8471 | h8471
                        · rcases p8384_3 (m.d 1 2) (by simp) with h8472 | h8472
                          · linarith only [h8201, h8472, hlam]
                          · rcases p8384_3 (m.d 1 3) (by simp) with h8474 | h8474
                            · rcases p8384_3 (m.d 1 4) (by simp) with h8475 | h8475
                              · linarith only [h8217, h8475, hlam]
                              · rcases p8384_3 (m.d 1 5) (by simp) with h8477 | h8477
                                · linarith only [h8218, h8477, hlam]
                                · linarith only [h8219, h8477, hlam]
                            · linarith only [h8217, h8474, hlam]
                        · linarith only [h2, h8471, hlam]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        rcases p8384_3 (m.d 0 1) (by simp) with h8482 | h8482
                        · rcases p8384_3 (m.d 1 2) (by simp) with h8483 | h8483
                          · linarith only [h8201, h8483, hlam]
                          · rcases p8384_3 (m.d 1 3) (by simp) with h8485 | h8485
                            · rcases p8384_3 (m.d 1 4) (by simp) with h8486 | h8486
                              · linarith only [h8217, h8486, hlam]
                              · rcases p8384_3 (m.d 1 5) (by simp) with h8488 | h8488
                                · linarith only [h8218, h8488, hlam]
                                · rcases h3bigk with h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c | h8490c
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [hlam, p8490_0]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [h4, h8203, h8219, hc12, hc23, hlam, hphi, p8384_1, p8490_1]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [h4, hlam, p8490_1]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    rcases p8490_3 (m.d 0 3) (by simp) with h8494 | h8494
                                    · rcases p8490_3 (m.d 1 3) (by simp) with h8495 | h8495
                                      · linarith only [h1, h8495, hlam]
                                      · linarith only [h8217, h8495, hlam]
                                    · linarith only [h8494, hlam, p8490_0]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    rcases p8490_3 (m.d 0 3) (by simp) with h8499 | h8499
                                    · rcases p8490_3 (m.d 1 3) (by simp) with h8500 | h8500
                                      · linarith only [h1, h8500, hlam]
                                      · linarith only [h8218, h8500, hlam]
                                    · linarith only [h8499, hlam, p8490_0]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [h1, hlam, p8490_0]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [hlam, p8490_0]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [h8201, hlam, p8490_1]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8490_1]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p8490_1]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [h1, h8203, h8219, hc12, hc23, hlam, hphi, p8384_1, p8490_1]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [h8203, h8219, hc12, hc23, hlam, hphi, p8384_1, p8490_1]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [hlam, p8490_0]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    rcases p8490_3 (m.d 0 3) (by simp) with h8512 | h8512
                                    · linarith only [h4, h8512, hlam]
                                    · linarith only [h7232, h8512, hlam]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    rcases p8490_3 (m.d 0 3) (by simp) with h8515 | h8515
                                    · linarith only [h4, h8515, hlam]
                                    · linarith only [h7233, h8515, hlam]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [h7232, hlam, p8490_0]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [h8217, hlam, p8490_0]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [h8221, hlam, p8490_0]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [hlam, p8490_0]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [h8382, hlam, p8490_1]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [h7233, hlam, p8490_0]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [h8218, hlam, p8490_0]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [h8222, hlam, p8490_0]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [h7233, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p8490_1]
                                  · have p8490_0 := h8490c.1
                                    have p8490_1 := h8490c.2.1
                                    have p8490_2 := h8490c.2.2.1
                                    have p8490_3 := h8490c.2.2.2
                                    linarith only [hlam, p8490_0]
                            · linarith only [h8218, h8485, hlam]
                        · linarith only [h3, h8482, hlam]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        linarith only [h2, hlam, p8384_0]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        linarith only [h2, h6364, h8223, hc12, hc45, hlam, hphi, ht23, ht34, p8384_1]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        linarith only [h8217, hlam, p8384_0]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        linarith only [hlam, p8384_0]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        linarith only [h8219, hlam, p8384_1]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        linarith only [h3, hlam, p8384_0]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        rcases p8384_3 (m.d 0 1) (by simp) with h8536 | h8536
                        · rcases p8384_3 (m.d 1 2) (by simp) with h8537 | h8537
                          · linarith only [h8205, h8537, hlam]
                          · rcases p8384_3 (m.d 1 3) (by simp) with h8539 | h8539
                            · rcases p8384_3 (m.d 1 4) (by simp) with h8540 | h8540
                              · linarith only [h8219, h8540, hlam]
                              · linarith only [h8203, h8540, hlam]
                            · linarith only [h8201, h8539, hlam]
                        · linarith only [h0, h8536, hlam]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        linarith only [h8218, hlam, p8384_0]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        rcases p8384_3 (m.d 0 1) (by simp) with h8546 | h8546
                        · rcases p8384_3 (m.d 1 2) (by simp) with h8547 | h8547
                          · linarith only [h8205, h8547, hlam]
                          · rcases p8384_3 (m.d 1 3) (by simp) with h8549 | h8549
                            · rcases p8384_3 (m.d 1 4) (by simp) with h8550 | h8550
                              · linarith only [h8219, h8550, hlam]
                              · rcases p8384_3 (m.d 1 5) (by simp) with h8552 | h8552
                                · rcases h3bigk with h8553c | h8553c | h8553c | h8553c | h8553c | h8553c | h8553c | h8553c | h8553c | h8553c | h8553c | h8553c | h8553c | h8553c | h8553c | h8553c | h8553c | h8553c | h8553c | h8553c | h8553c | h8553c | h8553c | h8553c | h8553c
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [hlam, p8553_0]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [h4, h8218, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8384_1, p8553_1]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [h4, hlam, p8553_1]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    rcases p8553_3 (m.d 0 3) (by simp) with h8557 | h8557
                                    · rcases p8553_3 (m.d 1 3) (by simp) with h8558 | h8558
                                      · linarith only [h1, h8558, hlam]
                                      · linarith only [h8217, h8558, hlam]
                                    · linarith only [h8557, hlam, p8553_0]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    rcases p8553_3 (m.d 0 3) (by simp) with h8562 | h8562
                                    · rcases p8553_3 (m.d 1 3) (by simp) with h8563 | h8563
                                      · linarith only [h1, h8563, hlam]
                                      · linarith only [h8218, h8563, hlam]
                                    · linarith only [h8562, hlam, p8553_0]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [h1, hlam, p8553_0]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [hlam, p8553_0]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [h8201, hlam, p8553_1]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8553_1]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [h1, h8382, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8553_1]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [h0, h4, hc12, hc23, hlam, hphi, p8553_1]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [h8201, hc12, hc23, hlam, hphi, p8553_1]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [hlam, p8553_0]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    rcases p8553_3 (m.d 0 3) (by simp) with h8575 | h8575
                                    · linarith only [h4, h8575, hlam]
                                    · linarith only [h7232, h8575, hlam]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    rcases p8553_3 (m.d 0 3) (by simp) with h8578 | h8578
                                    · linarith only [h4, h8578, hlam]
                                    · linarith only [h7233, h8578, hlam]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [h7232, hlam, p8553_0]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [h8217, hlam, p8553_0]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [h8221, hlam, p8553_0]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [hlam, p8553_0]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [h8382, hlam, p8553_1]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [h7233, hlam, p8553_0]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [h8218, hlam, p8553_0]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [h8222, hlam, p8553_0]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [h7233, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p8553_1]
                                  · have p8553_0 := h8553c.1
                                    have p8553_1 := h8553c.2.1
                                    have p8553_2 := h8553c.2.2.1
                                    have p8553_3 := h8553c.2.2.2
                                    linarith only [hlam, p8553_0]
                                · linarith only [h8219, h8552, hlam]
                            · linarith only [h8217, h8549, hlam]
                        · linarith only [h2, h8546, hlam]
                      · have p8384_0 := h8384c.1
                        have p8384_1 := h8384c.2.1
                        have p8384_2 := h8384c.2.2.1
                        have p8384_3 := h8384c.2.2.2
                        linarith only [hlam, p8384_0]
                · linarith only [h0, h1, h4, h8218, h8222, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
              · linarith only [h4, h7232, h8221, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h8597 | h8597
            · linarith only [h2, h7234, h8597, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h8599 | h8599
              · rcases m.htr 2 3 5 (by decide) (by decide) with h8600 | h8600
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8601 | h8601
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8602 | h8602
                    · linarith only [h7233, h7234, h8217, h8218, h8602, hlam]
                    · rcases h1bigk with h8604c | h8604c | h8604c | h8604c | h8604c | h8604c | h8604c | h8604c | h8604c | h8604c | h8604c | h8604c | h8604c | h8604c | h8604c | h8604c | h8604c | h8604c | h8604c | h8604c | h8604c | h8604c | h8604c | h8604c | h8604c
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [hlam, p8604_0]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        rcases p8604_3 (m.d 0 1) (by simp) with h8606 | h8606
                        · rcases p8604_3 (m.d 1 2) (by simp) with h8607 | h8607
                          · linarith only [h8607, hlam, p8604_0]
                          · rcases p8604_3 (m.d 1 3) (by simp) with h8609 | h8609
                            · linarith only [h1, h8609, hlam]
                            · linarith only [h8201, h8609, hlam]
                        · linarith only [h8606, hlam, p8604_0]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        rcases p8604_3 (m.d 0 1) (by simp) with h8613 | h8613
                        · rcases p8604_3 (m.d 1 2) (by simp) with h8614 | h8614
                          · linarith only [h0, h8614, hlam]
                          · rcases p8604_3 (m.d 1 3) (by simp) with h8616 | h8616
                            · linarith only [h8616, hlam, p8604_0]
                            · rcases p8604_3 (m.d 1 4) (by simp) with h8618 | h8618
                              · linarith only [h2, h8618, hlam]
                              · rcases p8604_3 (m.d 1 5) (by simp) with h8620 | h8620
                                · linarith only [h3, h8620, hlam]
                                · linarith only [h8218, h8620, hlam]
                        · linarith only [h8613, hlam, p8604_0]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        rcases p8604_3 (m.d 0 1) (by simp) with h8624 | h8624
                        · rcases p8604_3 (m.d 1 2) (by simp) with h8625 | h8625
                          · linarith only [h0, h8625, hlam]
                          · rcases p8604_3 (m.d 1 3) (by simp) with h8627 | h8627
                            · linarith only [h1, h8627, hlam]
                            · linarith only [h8217, h8627, hlam]
                        · linarith only [h8624, hlam, p8604_0]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        rcases p8604_3 (m.d 0 1) (by simp) with h8631 | h8631
                        · rcases p8604_3 (m.d 1 2) (by simp) with h8632 | h8632
                          · linarith only [h0, h8632, hlam]
                          · rcases p8604_3 (m.d 1 3) (by simp) with h8634 | h8634
                            · linarith only [h1, h8634, hlam]
                            · rcases p8604_3 (m.d 1 4) (by simp) with h8636 | h8636
                              · linarith only [h2, h8636, hlam]
                              · rcases p8604_3 (m.d 1 5) (by simp) with h8638 | h8638
                                · linarith only [h8638, hlam, p8604_0]
                                · rcases h3bigk with h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c | h8640c
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [hlam, p8640_0]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [h8217, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p8640_1]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [h4, hlam, p8640_1]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    rcases p8640_3 (m.d 0 3) (by simp) with h8644 | h8644
                                    · rcases p8640_3 (m.d 1 3) (by simp) with h8645 | h8645
                                      · linarith only [h1, h8645, hlam]
                                      · linarith only [h8217, h8645, hlam]
                                    · linarith only [h8644, hlam, p8640_0]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [h4, h8217, h8218, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8640_1]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [h1, hlam, p8640_0]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [hlam, p8640_0]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [h8201, hlam, p8640_1]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [h7233, h8218, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p8640_1]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [h8218, hlam, p8640_0]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [h0, h4, hc12, hc23, hlam, hphi, p8640_1]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [h8201, hc12, hc23, hlam, hphi, p8640_1]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [hlam, p8640_0]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    rcases p8640_3 (m.d 0 3) (by simp) with h8658 | h8658
                                    · linarith only [h4, h8658, hlam]
                                    · linarith only [h7232, h8658, hlam]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [h8217, h8218, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8640_1]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [h7232, hlam, p8640_0]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [h8217, hlam, p8640_0]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [h8599, hlam, p8640_0]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [hlam, p8640_0]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [h8602, hlam, p8640_1]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [h7233, hlam, p8640_0]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [h7233, h8217, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p8640_1]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [h8600, hlam, p8640_0]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [h7233, h7234, h8599, h8601, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8640_1]
                                  · have p8640_0 := h8640c.1
                                    have p8640_1 := h8640c.2.1
                                    have p8640_2 := h8640c.2.2.1
                                    have p8640_3 := h8640c.2.2.2
                                    linarith only [hlam, p8640_0]
                        · linarith only [h8631, hlam, p8604_0]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [h0, hlam, p8604_0]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [hlam, p8604_0]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [h8201, hlam, p8604_0]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [h8203, hlam, p8604_0]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [h8205, hlam, p8604_0]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [h1, hlam, p8604_0]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [h7233, h7234, h8218, h8599, h8601, hc12, hc23, hlam, hphi, p8604_1]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [hlam, p8604_0]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [h7233, h7234, h8203, h8218, h8599, h8601, hc12, hc23, hlam, hphi, p8604_1]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [h8218, hlam, p8604_1]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [h2, hlam, p8604_0]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [h2, h7234, h8599, h8601, hc12, hc23, hlam, hphi, p8604_1]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [h8217, hlam, p8604_0]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [hlam, p8604_0]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [h8597, hlam, p8604_1]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [h3, hlam, p8604_0]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [h3, h7234, h8599, h8601, hc12, hc23, hlam, hphi, p8604_1]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [h7233, h7234, h8201, h8218, h8599, h8601, hc12, hc23, hlam, hphi, p8604_1]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [h7233, h7234, h8203, h8218, h8599, h8601, hc12, hc23, hlam, hphi, p8604_1]
                      · have p8604_0 := h8604c.1
                        have p8604_1 := h8604c.2.1
                        have p8604_2 := h8604c.2.2.1
                        have p8604_3 := h8604c.2.2.2
                        linarith only [hlam, p8604_0]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8693 | h8693
                    · linarith only [h0, h6364, h8217, h8601, h8693, hc12, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases h1bigk with h8695c | h8695c | h8695c | h8695c | h8695c | h8695c | h8695c | h8695c | h8695c | h8695c | h8695c | h8695c | h8695c | h8695c | h8695c | h8695c | h8695c | h8695c | h8695c | h8695c | h8695c | h8695c | h8695c | h8695c | h8695c
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [hlam, p8695_0]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        rcases p8695_3 (m.d 0 1) (by simp) with h8697 | h8697
                        · rcases p8695_3 (m.d 1 2) (by simp) with h8698 | h8698
                          · linarith only [h8698, hlam, p8695_0]
                          · rcases p8695_3 (m.d 1 3) (by simp) with h8700 | h8700
                            · linarith only [h1, h8700, hlam]
                            · linarith only [h8201, h8700, hlam]
                        · linarith only [h8697, hlam, p8695_0]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        rcases p8695_3 (m.d 0 1) (by simp) with h8704 | h8704
                        · rcases p8695_3 (m.d 1 2) (by simp) with h8705 | h8705
                          · linarith only [h0, h8705, hlam]
                          · rcases p8695_3 (m.d 1 3) (by simp) with h8707 | h8707
                            · linarith only [h8707, hlam, p8695_0]
                            · rcases p8695_3 (m.d 1 4) (by simp) with h8709 | h8709
                              · linarith only [h2, h8709, hlam]
                              · rcases p8695_3 (m.d 1 5) (by simp) with h8711 | h8711
                                · linarith only [h3, h8711, hlam]
                                · linarith only [h8218, h8711, hlam]
                        · linarith only [h8704, hlam, p8695_0]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        rcases p8695_3 (m.d 0 1) (by simp) with h8715 | h8715
                        · rcases p8695_3 (m.d 1 2) (by simp) with h8716 | h8716
                          · linarith only [h0, h8716, hlam]
                          · rcases p8695_3 (m.d 1 3) (by simp) with h8718 | h8718
                            · linarith only [h1, h8718, hlam]
                            · linarith only [h8217, h8718, hlam]
                        · linarith only [h8715, hlam, p8695_0]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        rcases p8695_3 (m.d 0 1) (by simp) with h8722 | h8722
                        · rcases p8695_3 (m.d 1 2) (by simp) with h8723 | h8723
                          · linarith only [h0, h8723, hlam]
                          · rcases p8695_3 (m.d 1 3) (by simp) with h8725 | h8725
                            · linarith only [h1, h8725, hlam]
                            · rcases p8695_3 (m.d 1 4) (by simp) with h8727 | h8727
                              · linarith only [h2, h8727, hlam]
                              · rcases p8695_3 (m.d 1 5) (by simp) with h8729 | h8729
                                · linarith only [h8729, hlam, p8695_0]
                                · rcases h3bigk with h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c | h8731c
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [hlam, p8731_0]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [h4, h8217, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8731_1]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [h4, hlam, p8731_1]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    rcases p8731_3 (m.d 0 3) (by simp) with h8735 | h8735
                                    · rcases p8731_3 (m.d 1 3) (by simp) with h8736 | h8736
                                      · linarith only [h1, h8736, hlam]
                                      · linarith only [h8217, h8736, hlam]
                                    · linarith only [h8735, hlam, p8731_0]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [h4, h8217, h8218, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8731_1]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [h1, hlam, p8731_0]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [hlam, p8731_0]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [h8201, hlam, p8731_1]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p8731_1]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [h8218, hlam, p8731_0]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [h0, h4, hc12, hc23, hlam, hphi, p8731_1]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [h8201, hc12, hc23, hlam, hphi, p8731_1]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [hlam, p8731_0]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    rcases p8731_3 (m.d 0 3) (by simp) with h8749 | h8749
                                    · linarith only [h4, h8749, hlam]
                                    · linarith only [h7232, h8749, hlam]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [h8217, h8218, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8731_1]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [h7232, hlam, p8731_0]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [h8217, hlam, p8731_0]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [h8599, hlam, p8731_0]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [hlam, p8731_0]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [h8693, hlam, p8731_1]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [h7233, hlam, p8731_0]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [h7233, h8217, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p8731_1]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [h8600, hlam, p8731_0]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [h4, h7233, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8731_1]
                                  · have p8731_0 := h8731c.1
                                    have p8731_1 := h8731c.2.1
                                    have p8731_2 := h8731c.2.2.1
                                    have p8731_3 := h8731c.2.2.2
                                    linarith only [hlam, p8731_0]
                        · linarith only [h8722, hlam, p8695_0]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [h0, hlam, p8695_0]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [hlam, p8695_0]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [h8201, hlam, p8695_0]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [h8203, hlam, p8695_0]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [h8205, hlam, p8695_0]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [h1, hlam, p8695_0]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [h4, h7233, h8218, hc12, hc23, hlam, hphi, p8695_1]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [hlam, p8695_0]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [h4, h7233, h8218, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8695_1]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [h8218, hlam, p8695_1]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [h2, hlam, p8695_0]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [h2, h6364, h8601, hc12, hc45, hlam, hphi, ht23, ht34, p8695_1]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [h8217, hlam, p8695_0]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [hlam, p8695_0]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [h8597, hlam, p8695_1]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [h3, hlam, p8695_0]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [h4, h7233, h8218, hc12, hc23, hlam, hphi, p8695_1]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [h4, h7233, h8201, h8218, hc12, hc23, hlam, hphi, p8695_1]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [h4, h7233, h8203, h8218, hc12, hc23, hlam, hphi, p8695_1]
                      · have p8695_0 := h8695c.1
                        have p8695_1 := h8695c.2.1
                        have p8695_2 := h8695c.2.2.1
                        have p8695_3 := h8695c.2.2.2
                        linarith only [hlam, p8695_0]
                · linarith only [h4, h7233, h8600, hlam]
              · linarith only [h1, h4, h7233, h8217, h8218, h8599, hc01, hc15, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 1 3 5 (by decide) (by decide) with h8786 | h8786
          · rcases m.htr 1 4 5 (by decide) (by decide) with h8787 | h8787
            · linarith only [h2, h7234, h8787, hlam]
            · linarith only [h8217, h8786, h8787, hlam]
          · rcases m.htr 1 4 5 (by decide) (by decide) with h8790 | h8790
            · linarith only [h2, h7234, h8790, hlam]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h8792 | h8792
              · rcases m.htr 2 3 5 (by decide) (by decide) with h8793 | h8793
                · rcases m.htr 2 4 5 (by decide) (by decide) with h8794 | h8794
                  · linarith only [h7232, h7234, h8201, h8217, h8794, hc12, hc24, hlam, hphi]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h8796 | h8796
                    · linarith only [h1, h6364, h7232, h8794, h8796, hc01, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases h1bigk with h8798c | h8798c | h8798c | h8798c | h8798c | h8798c | h8798c | h8798c | h8798c | h8798c | h8798c | h8798c | h8798c | h8798c | h8798c | h8798c | h8798c | h8798c | h8798c | h8798c | h8798c | h8798c | h8798c | h8798c | h8798c
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [hlam, p8798_0]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        rcases p8798_3 (m.d 0 1) (by simp) with h8800 | h8800
                        · rcases p8798_3 (m.d 1 2) (by simp) with h8801 | h8801
                          · linarith only [h8801, hlam, p8798_0]
                          · rcases p8798_3 (m.d 1 3) (by simp) with h8803 | h8803
                            · linarith only [h1, h8803, hlam]
                            · linarith only [h8201, h8803, hlam]
                        · linarith only [h8800, hlam, p8798_0]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        rcases p8798_3 (m.d 0 1) (by simp) with h8807 | h8807
                        · rcases p8798_3 (m.d 1 2) (by simp) with h8808 | h8808
                          · linarith only [h0, h8808, hlam]
                          · rcases p8798_3 (m.d 1 3) (by simp) with h8810 | h8810
                            · linarith only [h8810, hlam, p8798_0]
                            · rcases p8798_3 (m.d 1 4) (by simp) with h8812 | h8812
                              · linarith only [h2, h8812, hlam]
                              · linarith only [h8217, h8812, hlam]
                        · linarith only [h8807, hlam, p8798_0]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        rcases p8798_3 (m.d 0 1) (by simp) with h8816 | h8816
                        · rcases p8798_3 (m.d 1 2) (by simp) with h8817 | h8817
                          · linarith only [h0, h8817, hlam]
                          · rcases p8798_3 (m.d 1 3) (by simp) with h8819 | h8819
                            · linarith only [h1, h8819, hlam]
                            · rcases p8798_3 (m.d 1 4) (by simp) with h8821 | h8821
                              · linarith only [h8821, hlam, p8798_0]
                              · rcases p8798_3 (m.d 1 5) (by simp) with h8823 | h8823
                                · linarith only [h3, h8823, hlam]
                                · linarith only [h8790, h8823, hlam]
                        · linarith only [h8816, hlam, p8798_0]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        rcases p8798_3 (m.d 0 1) (by simp) with h8827 | h8827
                        · rcases p8798_3 (m.d 1 2) (by simp) with h8828 | h8828
                          · linarith only [h0, h8828, hlam]
                          · rcases p8798_3 (m.d 1 3) (by simp) with h8830 | h8830
                            · linarith only [h1, h8830, hlam]
                            · rcases p8798_3 (m.d 1 4) (by simp) with h8832 | h8832
                              · linarith only [h2, h8832, hlam]
                              · rcases p8798_3 (m.d 1 5) (by simp) with h8834 | h8834
                                · linarith only [h8834, hlam, p8798_0]
                                · rcases h3bigk with h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c | h8836c
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [hlam, p8836_0]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h4, h8201, hc12, hc23, hlam, hphi, p8836_1]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h4, hlam, p8836_1]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h4, h8201, h8217, hc12, hc23, hlam, hphi, p8836_1]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h4, h8201, h8786, hc12, hc23, hlam, hphi, p8836_1]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h1, hlam, p8836_0]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [hlam, p8836_0]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h8201, hlam, p8836_1]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h8217, hlam, p8836_0]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h8786, hlam, p8836_0]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h1, h8201, hc12, hc23, hlam, hphi, p8836_1]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h8201, hc12, hc23, hlam, hphi, p8836_1]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [hlam, p8836_0]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h8201, h8217, hc12, hc23, hlam, hphi, p8836_1]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h8201, h8786, hc12, hc23, hlam, hphi, p8836_1]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h7232, hlam, p8836_0]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h7232, h8201, hc03, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p8836_1]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h8792, hlam, p8836_0]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [hlam, p8836_0]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h8796, hlam, p8836_1]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h7233, hlam, p8836_0]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h8201, hc12, hc35, hlam, hphi, ht23, p8836_1]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h8793, hlam, p8836_0]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [h4, h7233, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p8836_1]
                                  · have p8836_0 := h8836c.1
                                    have p8836_1 := h8836c.2.1
                                    have p8836_2 := h8836c.2.2.1
                                    have p8836_3 := h8836c.2.2.2
                                    linarith only [hlam, p8836_0]
                        · linarith only [h8827, hlam, p8798_0]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [h0, hlam, p8798_0]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [hlam, p8798_0]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [h8201, hlam, p8798_0]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [h8203, hlam, p8798_0]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [h8205, hlam, p8798_0]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [h1, hlam, p8798_0]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [h2, h6364, h8217, h8794, hc12, hc45, hlam, hphi, ht23, ht34, p8798_1]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [hlam, p8798_0]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [h8217, hlam, p8798_1]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [h8786, hlam, p8798_1]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [h2, hlam, p8798_0]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [h2, h6364, h8794, hc12, hc45, hlam, hphi, ht23, ht34, p8798_1]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [h2, h6364, h8794, hc13, hc45, hlam, hphi, ht34, p8798_1]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [hlam, p8798_0]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [h8790, hlam, p8798_1]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [h3, hlam, p8798_0]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [h4, h7233, h8786, hc12, hc23, hlam, hphi, p8798_1]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [h4, h7233, h8201, h8786, hc12, hc23, hlam, hphi, p8798_1]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [h4, h7233, h8203, h8786, hc12, hc23, hlam, hphi, p8798_1]
                      · have p8798_0 := h8798c.1
                        have p8798_1 := h8798c.2.1
                        have p8798_2 := h8798c.2.2.1
                        have p8798_3 := h8798c.2.2.2
                        linarith only [hlam, p8798_0]
                · linarith only [h4, h7233, h8793, hlam]
              · linarith only [h4, h7232, h8792, hlam]

set_option maxHeartbeats 5858000 in
set_option maxHeartbeats 5858000 in
theorem r1l7_11_23_L_I_H_I_s10_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (hg6364 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h7232 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h7233 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h3bigk := hb3.1
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  have h4 := hg4
  have h6364 := hg6364
  rcases m.htr 0 4 5 (by decide) (by decide) with h7234 | h7234
  · exact r1l7_11_23_L_I_H_I_s10_x0_x0_x0 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg6364 h7232 h7233 h7234
  · exact r1l7_11_23_L_I_H_I_s10_x0_x0_x1 m hb1 hb3 hg0 hg1 hg2 hg3 hg4 hg6364 h7232 h7233 h7234

end R2N4
