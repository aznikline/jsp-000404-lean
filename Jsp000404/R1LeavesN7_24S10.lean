import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_24S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 6172000 in
set_option maxHeartbeats 6172000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h7 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 5 (by decide) (by decide) with h226 | h226
  · rcases m.htr 0 4 5 (by decide) (by decide) with h227 | h227
    · rcases m.htr 1 2 3 (by decide) (by decide) with h228 | h228
      · rcases m.htr 1 2 4 (by decide) (by decide) with h229 | h229
        · rcases m.htr 1 3 4 (by decide) (by decide) with h230 | h230
          · linarith only [h1, h230, h7, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h232 | h232
            · rcases m.htr 1 4 5 (by decide) (by decide) with h233 | h233
              · rcases m.htr 2 3 4 (by decide) (by decide) with h234 | h234
                · linarith only [h0, h234, h4, h7, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h236 | h236
                  · linarith only [h0, h229, h234, h236, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                  · linarith only [h1, h232, h236, h7, hc23, hc34, hlam, hphi]
              · linarith only [h227, h230, h232, h233, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
            · linarith only [h226, h232, h7, hc13, hc34, hlam, hphi]
        · linarith only [h0, h228, h229, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h242 | h242
        · linarith only [h0, h228, h242, h4, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h244 | h244
          · linarith only [h226, h244, h7, hc35, hlam, hphi, ht01, ht0b, ht5b, u1elo2]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h246 | h246
            · rcases m.htr 1 4 5 (by decide) (by decide) with h247 | h247
              · rcases m.htr 2 3 4 (by decide) (by decide) with h248 | h248
                · linarith only [h248, h4, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h250 | h250
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h251 | h251
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h252 | h252
                      · rcases h0bigk with h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c | h253c
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [hlam, p253_0]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [h228, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p253_1, u1elo0]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [h228, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p253_1, u1elo0]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [h228, h4, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p253_1, u1elo0]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          rcases p253_3 (m.d 0 1) (by simp) with h258 | h258
                          · rcases p253_3 (m.d 0 2) (by simp) with h259 | h259
                            · linarith only [h0, h259, hlam]
                            · linarith only [h259, h6, hlam]
                          · linarith only [h258, h3, hlam]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [h0, hlam, p253_0]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [hlam, p253_0]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [h228, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p253_1, u0elo1]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [h0, h228, h4, h7, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p253_1, u1elo0]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          rcases p253_3 (m.d 0 1) (by simp) with h267 | h267
                          · rcases p253_3 (m.d 0 2) (by simp) with h268 | h268
                            · rcases p253_3 (m.d 0 3) (by simp) with h269 | h269
                              · linarith only [h269, h4, hlam]
                              · linarith only [h226, h269, hlam]
                            · linarith only [h268, h6, hlam]
                          · linarith only [h267, h3, hlam]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [h1, hlam, p253_1]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [h4, hlam, p253_1]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [hlam, p253_0]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [h7, hlam, p253_1]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          rcases p253_3 (m.d 0 1) (by simp) with h278 | h278
                          · rcases p253_3 (m.d 0 2) (by simp) with h279 | h279
                            · rcases p253_3 (m.d 0 3) (by simp) with h280 | h280
                              · rcases p253_3 (m.d 0 4) (by simp) with h281 | h281
                                · rcases p253_3 (m.d 0 5) (by simp) with h282 | h282
                                  · linarith only [h226, h282, hlam]
                                  · rcases h3bigk with h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c | h284c
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h246, h252, h7, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p284_1]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h228, h7, hc12, hc34, hlam, hphi, ht23, p284_1]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h7, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      rcases p284_3 (m.d 0 3) (by simp) with h289 | h289
                                      · rcases p284_3 (m.d 1 3) (by simp) with h290 | h290
                                        · linarith only [h1, h290, hlam]
                                        · linarith only [h246, h290, hlam]
                                      · linarith only [h289, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h1, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h228, hlam, p284_1]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h244, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h1, h252, hc45, hlam, hphi, ht01, ht0b, ht5b, p284_1, u1elo0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h4, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h0, h248, h5, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p284_1, u1elo0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h248, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h0, h248, h252, h5, hc45, hlam, hphi, ht01, ht0b, ht5b, p284_1, u1elo0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h0, h228, h246, h248, h252, h3, h5, hc12, hc34, hc45, hlam, hphi, ht01, ht0b, ht23, ht5b, p253_1, p284_1, u1elo0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      rcases p284_3 (m.d 0 3) (by simp) with h305 | h305
                                      · linarith only [h305, h7, hlam]
                                      · linarith only [h1, h305, hlam]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h228, hc12, hc34, hlam, hphi, ht23, p284_1]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h246, h3, h7, hlam, p253_1, p284_2]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h226, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h246, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h250, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [h252, hlam, p284_0]
                                    · have p284_0 := h284c.1
                                      have p284_1 := h284c.2.1
                                      have p284_2 := h284c.2.2.1
                                      have p284_3 := h284c.2.2.2
                                      linarith only [hlam, p284_0]
                                · linarith only [h227, h281, hlam]
                              · linarith only [h226, h280, hlam]
                            · linarith only [h279, h6, hlam]
                          · linarith only [h278, h3, hlam]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [h2, hlam, p253_0]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [h5, hlam, p253_0]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [h1, h246, h252, hc45, hlam, hphi, ht0b, ht5b, p253_1, u0elo3]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [hlam, p253_0]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          rcases p253_3 (m.d 0 1) (by simp) with h324 | h324
                          · rcases p253_3 (m.d 0 2) (by simp) with h325 | h325
                            · rcases p253_3 (m.d 0 3) (by simp) with h326 | h326
                              · linarith only [h326, h7, hlam]
                              · linarith only [h226, h326, hlam]
                            · linarith only [h325, h6, hlam]
                          · linarith only [h3, h324, hlam]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [h3, hlam, p253_0]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [h6, hlam, p253_1]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [h226, hlam, p253_0]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [h227, hlam, p253_1]
                        · have p253_0 := h253c.1
                          have p253_1 := h253c.2.1
                          have p253_2 := h253c.2.2.1
                          have p253_3 := h253c.2.2.2
                          linarith only [hlam, p253_0]
                      · linarith only [h228, h252, h4, h7, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h228, h247, h248, h251, h3, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                  · linarith only [h226, h228, h250, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h227, h244, h246, h247, h5, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
            · linarith only [h226, h246, h7, hc13, hc34, hlam, hphi]
    · linarith only [h226, h227, h7, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h342 | h342
    · rcases m.htr 1 2 3 (by decide) (by decide) with h343 | h343
      · rcases m.htr 1 2 4 (by decide) (by decide) with h344 | h344
        · rcases m.htr 1 3 4 (by decide) (by decide) with h345 | h345
          · linarith only [h1, h345, h7, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h347 | h347
            · linarith only [h1, h226, h347, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h349 | h349
              · rcases m.htr 2 3 4 (by decide) (by decide) with h350 | h350
                · linarith only [h1, h343, h350, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h352 | h352
                  · linarith only [h1, h226, h343, h352, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h354 | h354
                    · linarith only [h0, h344, h354, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                    · linarith only [h2, h349, h354, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h357 | h357
                · linarith only [h342, h343, h345, h349, h357, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h359 | h359
                  · linarith only [h226, h342, h343, h345, h349, h359, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h361 | h361
                    · linarith only [h343, h345, h349, h361, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h363 | h363
                      · rcases h0bigk with h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c | h364c
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [hlam, p364_0]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p364_1, u1elo0]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          rcases p364_3 (m.d 0 1) (by simp) with h367 | h367
                          · rcases p364_3 (m.d 0 2) (by simp) with h368 | h368
                            · linarith only [h0, h368, hlam]
                            · linarith only [h368, h4, hlam]
                          · linarith only [h1, h367, hlam]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [h342, h343, h345, h349, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p364_1, u1elo0]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [h342, h343, h345, h349, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p364_1, u1elo0]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [h0, hlam, p364_0]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [hlam, p364_0]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          rcases p364_3 (m.d 0 1) (by simp) with h376 | h376
                          · rcases p364_3 (m.d 0 2) (by simp) with h377 | h377
                            · rcases p364_3 (m.d 0 3) (by simp) with h378 | h378
                              · linarith only [h378, h4, hlam]
                              · rcases p364_3 (m.d 0 4) (by simp) with h380 | h380
                                · linarith only [h380, h5, hlam]
                                · linarith only [h380, h7, hlam]
                            · linarith only [h377, h4, hlam]
                          · linarith only [h1, h376, hlam]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [h342, h343, h345, h349, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p364_1, u0elo1]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [h0, h342, h343, h345, h349, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p364_1, u1elo0]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [h1, hlam, p364_1]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [h4, hlam, p364_1]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [hlam, p364_0]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [h7, hlam, p364_1]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [h226, hlam, p364_1]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [h2, hlam, p364_0]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [h5, hlam, p364_0]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          rcases p364_3 (m.d 0 1) (by simp) with h394 | h394
                          · rcases p364_3 (m.d 0 2) (by simp) with h395 | h395
                            · rcases p364_3 (m.d 0 3) (by simp) with h396 | h396
                              · linarith only [h396, h7, hlam]
                              · rcases p364_3 (m.d 0 4) (by simp) with h398 | h398
                                · rcases p364_3 (m.d 0 5) (by simp) with h399 | h399
                                  · linarith only [h342, h399, hlam]
                                  · linarith only [h226, h399, hlam]
                                · linarith only [h398, h7, hlam]
                            · linarith only [h395, h4, hlam]
                          · linarith only [h1, h394, hlam]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [hlam, p364_0]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [h342, h343, h345, h349, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p364_1, u0elo3]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [h3, hlam, p364_0]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [h6, hlam, p364_1]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          rcases p364_3 (m.d 0 1) (by simp) with h409 | h409
                          · rcases p364_3 (m.d 0 2) (by simp) with h410 | h410
                            · rcases p364_3 (m.d 0 3) (by simp) with h411 | h411
                              · linarith only [h226, h411, hlam]
                              · rcases p364_3 (m.d 0 4) (by simp) with h413 | h413
                                · rcases p364_3 (m.d 0 5) (by simp) with h414 | h414
                                  · rcases h3bigk with h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c | h415c
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      linarith only [hlam, p415_0]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      linarith only [h343, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p364_1, p415_1, u0elo4]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      linarith only [h3, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p364_1, p415_1, u1elo0]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      linarith only [h7, hlam, p415_0]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      linarith only [h226, hlam, p415_0]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      linarith only [h1, hlam, p415_0]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      linarith only [hlam, p415_0]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      linarith only [h345, h349, hc23, hc45, hlam, hphi, ht34, p415_1]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      linarith only [h345, hlam, p415_0]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      linarith only [h347, hlam, p415_0]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      linarith only [h4, hlam, p415_0]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      linarith only [h343, hlam, p415_0]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      linarith only [hlam, p415_0]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      linarith only [h357, hlam, p415_0]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      linarith only [h359, hlam, p415_0]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      rcases p415_3 (m.d 0 3) (by simp) with h431 | h431
                                      · linarith only [h431, hlam, p415_0]
                                      · rcases p415_3 (m.d 1 3) (by simp) with h433 | h433
                                        · linarith only [h345, h433, hlam]
                                        · rcases p415_3 (m.d 2 3) (by simp) with h435 | h435
                                          · linarith only [h357, h435, hlam]
                                          · rcases p415_3 (m.d 3 4) (by simp) with h437 | h437
                                            · rcases p415_3 (m.d 3 5) (by simp) with h438 | h438
                                              · linarith only [h363, h438, hlam]
                                              · linarith only [h226, h438, hlam]
                                            · linarith only [h437, hlam, p415_0]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      rcases p415_3 (m.d 0 3) (by simp) with h442 | h442
                                      · linarith only [h442, h7, hlam]
                                      · linarith only [h1, h442, hlam]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      rcases p415_3 (m.d 0 3) (by simp) with h445 | h445
                                      · linarith only [h445, h7, hlam]
                                      · linarith only [h4, h445, hlam]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      linarith only [hlam, p415_0]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      linarith only [h226, hc03, hc34, hlam, hphi, p364_1, p415_1]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      rcases p415_3 (m.d 0 3) (by simp) with h450 | h450
                                      · linarith only [h450, hlam, p415_0]
                                      · rcases p415_3 (m.d 1 3) (by simp) with h452 | h452
                                        · linarith only [h347, h452, hlam]
                                        · rcases p415_3 (m.d 2 3) (by simp) with h454 | h454
                                          · linarith only [h359, h454, hlam]
                                          · rcases p415_3 (m.d 3 4) (by simp) with h456 | h456
                                            · rcases p415_3 (m.d 3 5) (by simp) with h457 | h457
                                              · rcases h4bigk with h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c | h458c
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [hlam, p458_0]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  rcases p458_3 (m.d 0 4) (by simp) with h460 | h460
                                                  · rcases p458_3 (m.d 1 4) (by simp) with h461 | h461
                                                    · linarith only [h2, h461, hlam]
                                                    · rcases p458_3 (m.d 2 4) (by simp) with h463 | h463
                                                      · linarith only [h463, h5, hlam]
                                                      · rcases p458_3 (m.d 3 4) (by simp) with h465 | h465
                                                        · rcases p458_3 (m.d 4 5) (by simp) with h466 | h466
                                                          · linarith only [h342, h466, hlam]
                                                          · linarith only [h349, h466, hlam]
                                                        · linarith only [h345, h465, hlam]
                                                  · linarith only [h2, h460, hlam]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  rcases p458_3 (m.d 0 4) (by simp) with h471 | h471
                                                  · rcases p458_3 (m.d 1 4) (by simp) with h472 | h472
                                                    · linarith only [h2, h472, hlam]
                                                    · linarith only [h344, h472, hlam]
                                                  · linarith only [h471, h5, hlam]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [h7, hlam, p458_0]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [h0, h349, h5, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p458_1, u1elo0]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [h2, hlam, p458_1]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [hlam, p458_0]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [h349, hc24, hc45, hlam, hphi, p458_1]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [h345, hlam, p458_1]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [h349, hlam, p458_0]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [h5, hlam, p458_1]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [h344, hlam, p458_1]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [hlam, p458_0]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [h357, hlam, p458_1]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [h361, hlam, p458_0]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [h1, h342, h343, hc23, hc34, hlam, hphi, p364_1, p458_1]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  rcases p458_3 (m.d 0 4) (by simp) with h489 | h489
                                                  · linarith only [h489, h7, hlam]
                                                  · linarith only [h2, h489, hlam]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  rcases p458_3 (m.d 0 4) (by simp) with h492 | h492
                                                  · linarith only [h492, h7, hlam]
                                                  · linarith only [h492, h5, hlam]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [hlam, p458_0]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [h344, h349, h357, hc23, hc34, hlam, hphi, p458_1]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [h342, hlam, p458_0]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [h0, h342, h5, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b, p458_1, u1elo0]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [h0, h342, h357, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p458_1, u1elo0]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [h363, hlam, p458_0]
                                                · have p458_0 := h458c.1
                                                  have p458_1 := h458c.2.1
                                                  have p458_2 := h458c.2.2.1
                                                  have p458_3 := h458c.2.2.2
                                                  linarith only [hlam, p458_0]
                                              · linarith only [h457, hlam, p415_0]
                                            · linarith only [h456, h7, hlam]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      rcases p415_3 (m.d 0 3) (by simp) with h504 | h504
                                      · linarith only [h226, h504, hlam]
                                      · linarith only [h1, h504, hlam]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      rcases p415_3 (m.d 0 3) (by simp) with h507 | h507
                                      · linarith only [h226, h507, hlam]
                                      · linarith only [h4, h507, hlam]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      linarith only [h363, hlam, p415_0]
                                    · have p415_0 := h415c.1
                                      have p415_1 := h415c.2.1
                                      have p415_2 := h415c.2.2.1
                                      have p415_3 := h415c.2.2.2
                                      linarith only [hlam, p415_0]
                                  · linarith only [h226, h414, hlam]
                                · linarith only [h413, h7, hlam]
                            · linarith only [h4, h410, hlam]
                          · linarith only [h1, h409, hlam]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [h342, hlam, p364_1]
                        · have p364_0 := h364c.1
                          have p364_1 := h364c.2.1
                          have p364_2 := h364c.2.2.1
                          have p364_3 := h364c.2.2.2
                          linarith only [hlam, p364_0]
                      · linarith only [h0, h342, h363, h5, h7, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
        · linarith only [h0, h343, h344, h5, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h520 | h520
        · linarith only [h0, h343, h4, h520, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h522 | h522
          · linarith only [h343, h4, h522, h7, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h524 | h524
            · linarith only [h226, h343, h4, h524, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h526 | h526
              · rcases m.htr 2 3 4 (by decide) (by decide) with h527 | h527
                · linarith only [h4, h527, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h529 | h529
                  · linarith only [h226, h4, h529, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h531 | h531
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h532 | h532
                      · rcases h0bigk with h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c | h533c
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [hlam, p533_0]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h343, h5, h529, h531, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p533_1, u0elo0]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h343, h4, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p533_1, u1elo0]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h2, h526, hc45, hlam, hphi, ht01, ht0b, ht5b, p533_1, u1elo0]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h343, h529, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p533_1, u1elo0]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h0, hlam, p533_0]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [hlam, p533_0]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h343, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p533_1, u0elo1]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h0, h343, h5, h529, h531, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p533_1, u1elo0]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h0, h343, h529, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p533_1, u1elo0]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h1, hlam, p533_1]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h4, hlam, p533_1]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [hlam, p533_0]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h7, hlam, p533_1]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h226, hlam, p533_1]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h2, hlam, p533_0]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h5, hlam, p533_0]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h343, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p533_1, u0elo3]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [hlam, p533_0]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h0, h343, h5, h529, h6, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p533_1, u1elo0]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h3, hlam, p533_0]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h6, hlam, p533_1]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h343, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p533_1, u0elo4]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [h342, hlam, p533_1]
                        · have p533_0 := h533c.1
                          have p533_1 := h533c.2.1
                          have p533_2 := h533c.2.2.1
                          have p533_3 := h533c.2.2.2
                          linarith only [hlam, p533_0]
                      · linarith only [h2, h526, h532, h7, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · linarith only [h520, h526, h531, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h561 | h561
                · linarith only [h342, h343, h4, h522, h526, h561, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h563 | h563
                  · linarith only [h0, h226, h5, h561, h563, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h565 | h565
                    · linarith only [h0, h343, h5, h522, h526, h565, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
                    · linarith only [h342, h520, h565, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h568 | h568
      · rcases m.htr 1 2 4 (by decide) (by decide) with h569 | h569
        · rcases m.htr 1 3 4 (by decide) (by decide) with h570 | h570
          · linarith only [h1, h570, h7, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h572 | h572
            · linarith only [h1, h226, h572, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h574 | h574
              · linarith only [h2, h342, h574, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h576 | h576
                · linarith only [h1, h568, h576, h7, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h578 | h578
                  · linarith only [h1, h226, h568, h578, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h580 | h580
                    · linarith only [h0, h342, h5, h580, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h582 | h582
                      · rcases h0bigk with h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c | h583c
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          linarith only [hlam, p583_0]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          linarith only [h4, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p583_1, u1elo0]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          rcases p583_3 (m.d 0 1) (by simp) with h586 | h586
                          · rcases p583_3 (m.d 0 2) (by simp) with h587 | h587
                            · linarith only [h0, h587, hlam]
                            · linarith only [h4, h587, hlam]
                          · linarith only [h1, h586, hlam]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          rcases p583_3 (m.d 0 1) (by simp) with h591 | h591
                          · rcases p583_3 (m.d 0 2) (by simp) with h592 | h592
                            · linarith only [h0, h592, hlam]
                            · linarith only [h5, h592, hlam]
                          · linarith only [h2, h591, hlam]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          rcases p583_3 (m.d 0 1) (by simp) with h596 | h596
                          · rcases p583_3 (m.d 0 2) (by simp) with h597 | h597
                            · linarith only [h0, h597, hlam]
                            · linarith only [h597, h6, hlam]
                          · linarith only [h3, h596, hlam]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          linarith only [h0, hlam, p583_0]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          linarith only [hlam, p583_0]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          rcases p583_3 (m.d 0 1) (by simp) with h603 | h603
                          · rcases p583_3 (m.d 0 2) (by simp) with h604 | h604
                            · rcases p583_3 (m.d 0 3) (by simp) with h605 | h605
                              · linarith only [h4, h605, hlam]
                              · rcases p583_3 (m.d 0 4) (by simp) with h607 | h607
                                · linarith only [h5, h607, hlam]
                                · linarith only [h607, h7, hlam]
                            · linarith only [h4, h604, hlam]
                          · linarith only [h1, h603, hlam]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          rcases p583_3 (m.d 0 1) (by simp) with h612 | h612
                          · rcases p583_3 (m.d 0 2) (by simp) with h613 | h613
                            · rcases p583_3 (m.d 0 3) (by simp) with h614 | h614
                              · linarith only [h4, h614, hlam]
                              · rcases p583_3 (m.d 0 4) (by simp) with h616 | h616
                                · linarith only [h5, h616, hlam]
                                · rcases p583_3 (m.d 0 5) (by simp) with h618 | h618
                                  · linarith only [h6, h618, hlam]
                                  · linarith only [h342, h618, hlam]
                            · linarith only [h5, h613, hlam]
                          · linarith only [h2, h612, hlam]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          rcases p583_3 (m.d 0 1) (by simp) with h623 | h623
                          · rcases p583_3 (m.d 0 2) (by simp) with h624 | h624
                            · rcases p583_3 (m.d 0 3) (by simp) with h625 | h625
                              · linarith only [h4, h625, hlam]
                              · rcases p583_3 (m.d 0 4) (by simp) with h627 | h627
                                · linarith only [h5, h627, hlam]
                                · rcases p583_3 (m.d 0 5) (by simp) with h629 | h629
                                  · linarith only [h6, h629, hlam]
                                  · rcases h3bigk with h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c | h631c
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      linarith only [hlam, p631_0]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      linarith only [h342, h568, h7, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p583_1, p631_1, u0elo1]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      linarith only [h0, h342, h7, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p583_1, p631_1, u1elo0]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      linarith only [h7, hlam, p631_0]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      linarith only [h226, hlam, p631_0]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      linarith only [h1, hlam, p631_0]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      linarith only [hlam, p631_0]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      linarith only [h1, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p631_1, u1elo0]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      linarith only [h570, hlam, p631_0]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      linarith only [h572, hlam, p631_0]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      linarith only [h4, hlam, p631_0]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      linarith only [h568, hlam, p631_0]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      linarith only [hlam, p631_0]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      linarith only [h576, hlam, p631_0]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      linarith only [h578, hlam, p631_0]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      rcases p631_3 (m.d 0 3) (by simp) with h647 | h647
                                      · linarith only [h647, hlam, p631_0]
                                      · rcases p631_3 (m.d 1 3) (by simp) with h649 | h649
                                        · linarith only [h570, h649, hlam]
                                        · rcases p631_3 (m.d 2 3) (by simp) with h651 | h651
                                          · linarith only [h576, h651, hlam]
                                          · rcases p631_3 (m.d 3 4) (by simp) with h653 | h653
                                            · rcases p631_3 (m.d 3 5) (by simp) with h654 | h654
                                              · linarith only [h582, h654, hlam]
                                              · linarith only [h226, h654, hlam]
                                            · linarith only [h653, hlam, p631_0]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      rcases p631_3 (m.d 0 3) (by simp) with h658 | h658
                                      · linarith only [h658, h7, hlam]
                                      · linarith only [h1, h658, hlam]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      rcases p631_3 (m.d 0 3) (by simp) with h661 | h661
                                      · linarith only [h661, h7, hlam]
                                      · linarith only [h4, h661, hlam]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      linarith only [hlam, p631_0]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      linarith only [h342, h582, h7, hc03, hc34, hlam, hphi, p631_1]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      rcases p631_3 (m.d 0 3) (by simp) with h666 | h666
                                      · linarith only [h666, hlam, p631_0]
                                      · rcases p631_3 (m.d 1 3) (by simp) with h668 | h668
                                        · linarith only [h572, h668, hlam]
                                        · rcases p631_3 (m.d 2 3) (by simp) with h670 | h670
                                          · linarith only [h578, h670, hlam]
                                          · rcases p631_3 (m.d 3 4) (by simp) with h672 | h672
                                            · rcases p631_3 (m.d 3 5) (by simp) with h673 | h673
                                              · rcases h4bigk with h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c | h674c
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [hlam, p674_0]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [h0, h342, h568, h570, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p583_1, p674_1, u1elo0]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [h0, h342, h576, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p583_1, p674_1, u1elo0]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [h7, hlam, p674_0]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [h342, hlam, p674_0]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [h2, hlam, p674_1]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [hlam, p674_0]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [h2, h576, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p674_1, u1elo0]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [h570, hlam, p674_1]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [h574, hlam, p674_0]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [h5, hlam, p674_1]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [h569, hlam, p674_1]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [hlam, p674_0]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [h576, hlam, p674_1]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [h580, hlam, p674_0]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  rcases p674_3 (m.d 0 4) (by simp) with h690 | h690
                                                  · linarith only [h690, h7, hlam]
                                                  · rcases p674_3 (m.d 1 4) (by simp) with h692 | h692
                                                    · linarith only [h570, h692, hlam]
                                                    · rcases p674_3 (m.d 2 4) (by simp) with h694 | h694
                                                      · linarith only [h576, h694, hlam]
                                                      · rcases p674_3 (m.d 3 4) (by simp) with h696 | h696
                                                        · rcases p674_3 (m.d 4 5) (by simp) with h697 | h697
                                                          · linarith only [h582, h697, hlam]
                                                          · linarith only [h342, h697, hlam]
                                                        · linarith only [h696, h7, hlam]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  rcases p674_3 (m.d 0 4) (by simp) with h701 | h701
                                                  · linarith only [h7, h701, hlam]
                                                  · linarith only [h2, h701, hlam]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  rcases p674_3 (m.d 0 4) (by simp) with h704 | h704
                                                  · linarith only [h7, h704, hlam]
                                                  · linarith only [h5, h704, hlam]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [hlam, p674_0]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [h342, h7, hc03, hc34, hlam, hphi, p674_1]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [h1, h568, h582, h7, hc23, hc34, hlam, hphi, p674_1]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [h569, h576, h582, hc23, hc34, hlam, hphi, p674_1]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [h576, h582, hc23, hc34, hlam, hphi, p674_1]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [h582, hlam, p674_0]
                                                · have p674_0 := h674c.1
                                                  have p674_1 := h674c.2.1
                                                  have p674_2 := h674c.2.2.1
                                                  have p674_3 := h674c.2.2.2
                                                  linarith only [hlam, p674_0]
                                              · linarith only [h673, hlam, p631_0]
                                            · linarith only [h672, h7, hlam]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      rcases p631_3 (m.d 0 3) (by simp) with h716 | h716
                                      · linarith only [h226, h716, hlam]
                                      · linarith only [h1, h716, hlam]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      rcases p631_3 (m.d 0 3) (by simp) with h719 | h719
                                      · linarith only [h226, h719, hlam]
                                      · linarith only [h4, h719, hlam]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      linarith only [h582, hlam, p631_0]
                                    · have p631_0 := h631c.1
                                      have p631_1 := h631c.2.1
                                      have p631_2 := h631c.2.2.1
                                      have p631_3 := h631c.2.2.2
                                      linarith only [hlam, p631_0]
                            · linarith only [h6, h624, hlam]
                          · linarith only [h3, h623, hlam]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          linarith only [h1, hlam, p583_1]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          linarith only [h4, hlam, p583_1]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          linarith only [hlam, p583_0]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          linarith only [h7, hlam, p583_1]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          linarith only [h226, hlam, p583_1]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          linarith only [h2, hlam, p583_0]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          linarith only [h5, hlam, p583_0]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          linarith only [h1, h342, h568, h582, hc23, hc34, hlam, hphi, p583_1]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          linarith only [hlam, p583_0]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          linarith only [h342, hlam, p583_0]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          linarith only [h3, hlam, p583_0]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          linarith only [h6, hlam, p583_1]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          linarith only [h1, h342, h568, h582, hc23, hc34, hlam, hphi, p583_1]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          linarith only [h2, h342, h569, h576, h582, hc23, hc34, hlam, hphi, p583_1]
                        · have p583_0 := h583c.1
                          have p583_1 := h583c.2.1
                          have p583_2 := h583c.2.2.1
                          have p583_3 := h583c.2.2.2
                          linarith only [hlam, p583_0]
                      · rcases h0bigk with h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c | h741c
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          linarith only [hlam, p741_0]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          linarith only [h6, hc25, hlam, hphi, ht01, ht0b, ht5b, p741_1, u1elo0]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          rcases p741_3 (m.d 0 1) (by simp) with h744 | h744
                          · rcases p741_3 (m.d 0 2) (by simp) with h745 | h745
                            · linarith only [h0, h745, hlam]
                            · linarith only [h4, h745, hlam]
                          · linarith only [h1, h744, hlam]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          rcases p741_3 (m.d 0 1) (by simp) with h749 | h749
                          · rcases p741_3 (m.d 0 2) (by simp) with h750 | h750
                            · linarith only [h0, h750, hlam]
                            · linarith only [h5, h750, hlam]
                          · linarith only [h2, h749, hlam]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          rcases p741_3 (m.d 0 1) (by simp) with h754 | h754
                          · rcases p741_3 (m.d 0 2) (by simp) with h755 | h755
                            · linarith only [h0, h755, hlam]
                            · linarith only [h6, h755, hlam]
                          · linarith only [h3, h754, hlam]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          linarith only [h0, hlam, p741_0]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          linarith only [hlam, p741_0]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          rcases p741_3 (m.d 0 1) (by simp) with h761 | h761
                          · rcases p741_3 (m.d 0 2) (by simp) with h762 | h762
                            · rcases p741_3 (m.d 0 3) (by simp) with h763 | h763
                              · linarith only [h4, h763, hlam]
                              · rcases p741_3 (m.d 0 4) (by simp) with h765 | h765
                                · linarith only [h5, h765, hlam]
                                · linarith only [h7, h765, hlam]
                            · linarith only [h4, h762, hlam]
                          · linarith only [h1, h761, hlam]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          rcases p741_3 (m.d 0 1) (by simp) with h770 | h770
                          · rcases p741_3 (m.d 0 2) (by simp) with h771 | h771
                            · rcases p741_3 (m.d 0 3) (by simp) with h772 | h772
                              · linarith only [h4, h772, hlam]
                              · rcases p741_3 (m.d 0 4) (by simp) with h774 | h774
                                · linarith only [h5, h774, hlam]
                                · rcases p741_3 (m.d 0 5) (by simp) with h776 | h776
                                  · linarith only [h6, h776, hlam]
                                  · linarith only [h342, h776, hlam]
                            · linarith only [h5, h771, hlam]
                          · linarith only [h2, h770, hlam]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          rcases p741_3 (m.d 0 1) (by simp) with h781 | h781
                          · rcases p741_3 (m.d 0 2) (by simp) with h782 | h782
                            · rcases p741_3 (m.d 0 3) (by simp) with h783 | h783
                              · linarith only [h4, h783, hlam]
                              · rcases p741_3 (m.d 0 4) (by simp) with h785 | h785
                                · linarith only [h5, h785, hlam]
                                · rcases p741_3 (m.d 0 5) (by simp) with h787 | h787
                                  · linarith only [h6, h787, hlam]
                                  · rcases h3bigk with h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c | h789c
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [hlam, p789_0]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [h568, h582, h7, hc23, hc45, hlam, hphi, ht34, p789_1]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [h582, h7, hc23, hc45, hlam, hphi, ht34, p789_1]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [h7, hlam, p789_0]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [h226, hlam, p789_0]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [h1, hlam, p789_0]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [hlam, p789_0]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [h1, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p789_1, u1elo0]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [h570, hlam, p789_0]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [h572, hlam, p789_0]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [h4, hlam, p789_0]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [h568, hlam, p789_0]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [hlam, p789_0]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [h576, hlam, p789_0]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [h578, hlam, p789_0]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [h582, hc03, hc45, hlam, hphi, ht34, p789_1]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [h568, h582, hc23, hc45, hlam, hphi, ht34, p789_1]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [h582, hc23, hc45, hlam, hphi, ht34, p789_1]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [hlam, p789_0]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [h582, hlam, p789_1]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      rcases p789_3 (m.d 0 3) (by simp) with h810 | h810
                                      · linarith only [h810, hlam, p789_0]
                                      · rcases p789_3 (m.d 1 3) (by simp) with h812 | h812
                                        · linarith only [h572, h812, hlam]
                                        · rcases p789_3 (m.d 2 3) (by simp) with h814 | h814
                                          · linarith only [h578, h814, hlam]
                                          · rcases p789_3 (m.d 3 4) (by simp) with h816 | h816
                                            · linarith only [h582, h816, hlam]
                                            · linarith only [h7, h816, hlam]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      rcases p789_3 (m.d 0 3) (by simp) with h819 | h819
                                      · linarith only [h226, h819, hlam]
                                      · linarith only [h1, h819, hlam]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      rcases p789_3 (m.d 0 3) (by simp) with h822 | h822
                                      · linarith only [h226, h822, hlam]
                                      · linarith only [h4, h822, hlam]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [h1, h568, h7, hc23, hc35, hlam, hphi, p789_1]
                                    · have p789_0 := h789c.1
                                      have p789_1 := h789c.2.1
                                      have p789_2 := h789c.2.2.1
                                      have p789_3 := h789c.2.2.2
                                      linarith only [hlam, p789_0]
                            · linarith only [h6, h782, hlam]
                          · linarith only [h3, h781, hlam]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          linarith only [h1, hlam, p741_1]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          linarith only [h4, hlam, p741_1]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          linarith only [hlam, p741_0]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          linarith only [h7, hlam, p741_1]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          linarith only [h226, hlam, p741_1]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          linarith only [h2, hlam, p741_0]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          linarith only [h5, hlam, p741_0]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          linarith only [h1, h342, h568, hc23, hc45, hlam, hphi, ht34, p741_1]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          linarith only [hlam, p741_0]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          linarith only [h342, hlam, p741_0]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          linarith only [h3, hlam, p741_0]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          linarith only [h6, hlam, p741_1]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          rcases p741_3 (m.d 0 1) (by simp) with h841 | h841
                          · rcases p741_3 (m.d 0 2) (by simp) with h842 | h842
                            · rcases p741_3 (m.d 0 3) (by simp) with h843 | h843
                              · linarith only [h226, h843, hlam]
                              · rcases p741_3 (m.d 0 4) (by simp) with h845 | h845
                                · linarith only [h342, h845, hlam]
                                · linarith only [h7, h845, hlam]
                            · linarith only [h4, h842, hlam]
                          · linarith only [h1, h841, hlam]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          rcases p741_3 (m.d 0 1) (by simp) with h850 | h850
                          · rcases p741_3 (m.d 0 2) (by simp) with h851 | h851
                            · rcases p741_3 (m.d 0 3) (by simp) with h852 | h852
                              · linarith only [h226, h852, hlam]
                              · rcases p741_3 (m.d 0 4) (by simp) with h854 | h854
                                · linarith only [h342, h854, hlam]
                                · rcases p741_3 (m.d 0 5) (by simp) with h856 | h856
                                  · rcases h3bigk with h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c | h857c
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [hlam, p857_0]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [h568, h582, h7, hc23, hc45, hlam, hphi, ht34, p857_1]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [h582, h7, hc23, hc45, hlam, hphi, ht34, p857_1]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [h7, hlam, p857_0]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [h226, hlam, p857_0]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [h1, hlam, p857_0]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [hlam, p857_0]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [h1, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p857_1, u1elo0]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [h570, hlam, p857_0]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [h572, hlam, p857_0]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [h4, hlam, p857_0]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [h568, hlam, p857_0]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [hlam, p857_0]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [h576, hlam, p857_0]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [h578, hlam, p857_0]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [h582, hc03, hc45, hlam, hphi, ht34, p857_1]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [h568, h582, hc23, hc45, hlam, hphi, ht34, p857_1]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [h582, hc23, hc45, hlam, hphi, ht34, p857_1]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [hlam, p857_0]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [h582, hlam, p857_1]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      rcases p857_3 (m.d 0 3) (by simp) with h878 | h878
                                      · linarith only [h878, hlam, p857_0]
                                      · rcases p857_3 (m.d 1 3) (by simp) with h880 | h880
                                        · linarith only [h572, h880, hlam]
                                        · rcases p857_3 (m.d 2 3) (by simp) with h882 | h882
                                          · linarith only [h578, h882, hlam]
                                          · rcases p857_3 (m.d 3 4) (by simp) with h884 | h884
                                            · linarith only [h582, h884, hlam]
                                            · linarith only [h7, h884, hlam]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      rcases p857_3 (m.d 0 3) (by simp) with h887 | h887
                                      · linarith only [h226, h887, hlam]
                                      · linarith only [h1, h887, hlam]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      rcases p857_3 (m.d 0 3) (by simp) with h890 | h890
                                      · linarith only [h226, h890, hlam]
                                      · linarith only [h4, h890, hlam]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [h1, h568, h582, h7, hc23, hc45, hlam, hphi, ht34, p857_1]
                                    · have p857_0 := h857c.1
                                      have p857_1 := h857c.2.1
                                      have p857_2 := h857c.2.2.1
                                      have p857_3 := h857c.2.2.2
                                      linarith only [hlam, p857_0]
                                  · linarith only [h342, h856, hlam]
                            · linarith only [h5, h851, hlam]
                          · linarith only [h2, h850, hlam]
                        · have p741_0 := h741c.1
                          have p741_1 := h741c.2.1
                          have p741_2 := h741c.2.2.1
                          have p741_3 := h741c.2.2.2
                          linarith only [hlam, p741_0]
        · linarith only [h0, h5, h568, h569, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
      · rcases m.htr 1 2 4 (by decide) (by decide) with h900 | h900
        · linarith only [h0, h4, h568, h900, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h902 | h902
          · linarith only [h4, h568, h7, h902, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h904 | h904
            · linarith only [h0, h226, h4, h5, h568, h900, h902, h904, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h906 | h906
              · linarith only [h342, h5, h900, h906, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h908 | h908
                · linarith only [h4, h7, h908, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h910 | h910
                  · linarith only [h226, h4, h910, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h912 | h912
                    · linarith only [h342, h5, h912, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h914 | h914
                      · linarith only [h342, h4, h568, h7, h914, hc12, hc34, hlam, hphi, ht23]
                      · linarith only [h4, h568, h7, h914, hc12, hc45, hlam, hphi, ht23, ht34]

set_option maxHeartbeats 6172000 in
set_option maxHeartbeats 6172000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x0_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h5 h6 h7
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x0_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h5 h6 h7

set_option maxHeartbeats 6172000 in
set_option maxHeartbeats 6172000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 3 4 (by decide) (by decide) with h917 | h917
  · rcases m.htr 0 3 5 (by decide) (by decide) with h918 | h918
    · linarith only [h4, h6, h918, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h920 | h920
      · linarith only [h4, h6, h917, h920, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h922 | h922
        · rcases m.htr 1 2 4 (by decide) (by decide) with h923 | h923
          · rcases m.htr 1 3 4 (by decide) (by decide) with h924 | h924
            · rcases m.htr 1 3 5 (by decide) (by decide) with h925 | h925
              · linarith only [h1, h918, h925, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h927 | h927
                · linarith only [h2, h920, h927, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h929 | h929
                  · linarith only [h0, h922, h929, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                  · linarith only [h917, h918, h929, hc23, hc35, hlam, hphi]
            · linarith only [h917, h918, h924, hc13, hc35, hlam, hphi]
          · linarith only [h5, h6, h923, hc12, hc25, hlam, hphi]
        · linarith only [h4, h6, h922, hc12, hc25, hlam, hphi]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h935 | h935
    · linarith only [h4, h6, h935, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h937 | h937
      · linarith only [h5, h6, h937, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h939 | h939
        · rcases m.htr 1 2 4 (by decide) (by decide) with h940 | h940
          · rcases m.htr 1 3 4 (by decide) (by decide) with h941 | h941
            · linarith only [h1, h917, h941, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h943 | h943
              · linarith only [h0, h1, h6, h917, h935, h939, h943, hc23, hc34, hlam, hphi]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h945 | h945
                · linarith only [h2, h937, h945, hlam]
                · rcases m.htr 2 3 4 (by decide) (by decide) with h947 | h947
                  · linarith only [h0, h917, h939, h947, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 2 3 5 (by decide) (by decide) with h949 | h949
                    · linarith only [h4, h6, h935, h949, hlam]
                    · rcases m.htr 2 4 5 (by decide) (by decide) with h951 | h951
                      · linarith only [h0, h940, h951, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo0]
                      · rcases m.htr 3 4 5 (by decide) (by decide) with h953 | h953
                        · linarith only [h0, h6, h940, h947, h951, h953, hc23, hc34, hlam, hphi]
                        · rcases h0bigk with h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c | h955c
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h0, h940, h947, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p955_1, u1elo0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            rcases p955_3 (m.d 0 1) (by simp) with h958 | h958
                            · rcases p955_3 (m.d 0 2) (by simp) with h959 | h959
                              · linarith only [h0, h959, hlam]
                              · linarith only [h4, h959, hlam]
                            · linarith only [h1, h958, hlam]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            rcases p955_3 (m.d 0 1) (by simp) with h963 | h963
                            · rcases p955_3 (m.d 0 2) (by simp) with h964 | h964
                              · linarith only [h0, h964, hlam]
                              · linarith only [h5, h964, hlam]
                            · linarith only [h2, h963, hlam]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h0, h6, h940, h947, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p955_1, u1elo0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h0, hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h1, h6, h949, hc13, hc35, hlam, hphi, p955_1]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h6, h949, h953, hc04, hc45, hlam, hphi, p955_1]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h6, hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h1, hlam, p955_1]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h4, hlam, p955_1]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h917, hlam, p955_1]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h935, hlam, p955_1]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h2, hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h5, hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h1, h5, h6, h949, h953, hc13, hc45, hlam, hphi, ht34, p955_1]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h937, hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h3, hlam, p955_0]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [h0, h940, hc24, hlam, hphi, ht0b, ht45, ht5b, p955_1, u0elo4]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            rcases p955_3 (m.d 0 1) (by simp) with h986 | h986
                            · rcases p955_3 (m.d 0 2) (by simp) with h987 | h987
                              · linarith only [h6, h987, hlam]
                              · linarith only [h4, h987, hlam]
                            · linarith only [h1, h986, hlam]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            rcases p955_3 (m.d 0 1) (by simp) with h991 | h991
                            · rcases p955_3 (m.d 0 2) (by simp) with h992 | h992
                              · linarith only [h6, h992, hlam]
                              · linarith only [h5, h992, hlam]
                            · linarith only [h2, h991, hlam]
                          · have p955_0 := h955c.1
                            have p955_1 := h955c.2.1
                            have p955_2 := h955c.2.2.1
                            have p955_3 := h955c.2.2.2
                            linarith only [hlam, p955_0]
          · linarith only [h5, h6, h940, hc12, hc25, hlam, hphi]
        · linarith only [h4, h6, h939, hc12, hc25, hlam, hphi]

set_option maxHeartbeats 6172000 in
set_option maxHeartbeats 6172000 in
theorem r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h5 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
 : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
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
  have h0elo := hb0.1
  have h0bigk := hb0.2.2.2
  have h1elo := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  have h3 := hg3
  rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x0_x0_x0 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h5 h6
  · exact r1l7_20_11_13_14_M_LI_L_0_L_I_L_I_s3_x0_x0_x1 m hb0 hb1 hb3 hb4 hg0 hg1 hg2 hg3 h4 h5 h6

end R2N4
