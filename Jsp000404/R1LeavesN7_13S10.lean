import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_13S9

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7524000 in
set_option maxHeartbeats 7524000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6923 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7870 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8661 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8662 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8663 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8664 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8665 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
    (h8666 : (m.d 4 5 + m.lam ≤ m.d 0 4 ∧ m.d 4 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  have h6923 := hg6923
  have h7870 := hg7870
  rcases m.htr 1 2 3 (by decide) (by decide) with h9256 | h9256
  · rcases m.htr 1 2 4 (by decide) (by decide) with h9257 | h9257
    · rcases m.htr 1 2 5 (by decide) (by decide) with h9258 | h9258
      · rcases m.htr 1 3 4 (by decide) (by decide) with h9259 | h9259
        · rcases m.htr 1 3 5 (by decide) (by decide) with h9260 | h9260
          · rcases m.htr 1 4 5 (by decide) (by decide) with h9261 | h9261
            · rcases m.htr 2 3 4 (by decide) (by decide) with h9262 | h9262
              · rcases m.htr 2 3 5 (by decide) (by decide) with h9263 | h9263
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9264 | h9264
                  · linarith only [h8662, h8666, h9264, hlam]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9266 | h9266
                    · linarith only [h8661, h8666, h9262, h9266, hc02, hc04, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h2bigk with h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c | h9268c
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [hlam, p9268_0]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [h0, hlam, p9268_0]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [h0, h9263, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p9268_1]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        rcases p9268_3 (m.d 0 2) (by simp) with h9272 | h9272
                        · rcases p9268_3 (m.d 1 2) (by simp) with h9273 | h9273
                          · rcases p9268_3 (m.d 2 3) (by simp) with h9274 | h9274
                            · linarith only [h8661, h9274, hlam]
                            · linarith only [h9262, h9274, hlam]
                          · linarith only [h9257, h9273, hlam]
                        · linarith only [h9272, hlam, p9268_0]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        rcases p9268_3 (m.d 0 2) (by simp) with h9279 | h9279
                        · rcases p9268_3 (m.d 1 2) (by simp) with h9280 | h9280
                          · rcases p9268_3 (m.d 2 3) (by simp) with h9281 | h9281
                            · linarith only [h8661, h9281, hlam]
                            · linarith only [h9263, h9281, hlam]
                          · linarith only [h9258, h9280, hlam]
                        · linarith only [h9279, hlam, p9268_0]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p9268_1]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [hlam, p9268_0]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [h9263, h9266, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9268_1]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        rcases p9268_3 (m.d 0 2) (by simp) with h9289 | h9289
                        · linarith only [h0, h9289, hlam]
                        · linarith only [h8662, h9289, hlam]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        rcases p9268_3 (m.d 0 2) (by simp) with h9292 | h9292
                        · linarith only [h0, h9292, hlam]
                        · linarith only [h8663, h9292, hlam]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [h8661, hlam, p9268_0]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [h9256, hlam, p9268_0]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [hlam, p9268_0]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [h8661, h9262, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p9268_1]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [h0, h8661, h9262, h9264, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9268_1]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [h8662, hlam, p9268_0]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [h9257, hlam, p9268_0]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [h9262, hlam, p9268_0]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [hlam, p9268_0]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [h9264, hlam, p9268_0]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [h8663, hlam, p9268_0]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [h9258, hlam, p9268_0]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [h9263, hlam, p9268_0]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [h0, h8663, h9262, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9268_1]
                      · have p9268_0 := h9268c.1
                        have p9268_1 := h9268c.2.1
                        have p9268_2 := h9268c.2.2.1
                        have p9268_3 := h9268c.2.2.2
                        linarith only [hlam, p9268_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9310 | h9310
                  · linarith only [h0, h8662, h8665, h8666, h9262, h9263, h9310, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9312 | h9312
                    · linarith only [h8665, h8666, h9262, h9263, h9312, hc04, hc05, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h2bigk with h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c | h9314c
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [hlam, p9314_0]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [h0, hlam, p9314_0]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [h0, h9262, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9314_1]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        rcases p9314_3 (m.d 0 2) (by simp) with h9318 | h9318
                        · rcases p9314_3 (m.d 1 2) (by simp) with h9319 | h9319
                          · rcases p9314_3 (m.d 2 3) (by simp) with h9320 | h9320
                            · linarith only [h8661, h9320, hlam]
                            · linarith only [h9262, h9320, hlam]
                          · linarith only [h9257, h9319, hlam]
                        · linarith only [h9318, hlam, p9314_0]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [h0, h9262, h9263, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9314_1]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p9314_1]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [hlam, p9314_0]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [h9262, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9314_1]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        rcases p9314_3 (m.d 0 2) (by simp) with h9329 | h9329
                        · linarith only [h0, h9329, hlam]
                        · linarith only [h8662, h9329, hlam]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [h9262, h9263, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9314_1]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [h8661, hlam, p9314_0]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [h9256, hlam, p9314_0]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [hlam, p9314_0]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [h8661, h8665, h9262, h9263, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p9314_1]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [h9263, hlam, p9314_1]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [h8662, hlam, p9314_0]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [h9257, hlam, p9314_0]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [h9262, hlam, p9314_0]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [hlam, p9314_0]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [h9310, hlam, p9314_0]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [h8663, hlam, p9314_0]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [h9258, hlam, p9314_0]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [h0, h8663, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9314_1]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [h8665, h8666, h9256, h9259, h9261, h9262, h9263, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9314_1]
                      · have p9314_0 := h9314c.1
                        have p9314_1 := h9314c.2.1
                        have p9314_2 := h9314c.2.2.1
                        have p9314_3 := h9314c.2.2.2
                        linarith only [hlam, p9314_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h9348 | h9348
                · linarith only [h8664, h8666, h9256, h9259, h9261, h9262, h9348, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9350 | h9350
                  · linarith only [h0, h8662, h8664, h8666, h9262, h9350, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9352 | h9352
                    · linarith only [h8664, h8666, h9352, hlam]
                    · rcases h2bigk with h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c | h9354c
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        linarith only [hlam, p9354_0]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        linarith only [h0, hlam, p9354_0]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        rcases p9354_3 (m.d 0 2) (by simp) with h9357 | h9357
                        · rcases p9354_3 (m.d 1 2) (by simp) with h9358 | h9358
                          · rcases p9354_3 (m.d 2 3) (by simp) with h9359 | h9359
                            · linarith only [h9359, hlam, p9354_0]
                            · rcases p9354_3 (m.d 2 4) (by simp) with h9361 | h9361
                              · linarith only [h8662, h9361, hlam]
                              · linarith only [h9262, h9361, hlam]
                          · linarith only [h9256, h9358, hlam]
                        · linarith only [h9357, hlam, p9354_0]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        rcases p9354_3 (m.d 0 2) (by simp) with h9366 | h9366
                        · rcases p9354_3 (m.d 1 2) (by simp) with h9367 | h9367
                          · rcases p9354_3 (m.d 2 3) (by simp) with h9368 | h9368
                            · linarith only [h8661, h9368, hlam]
                            · rcases p9354_3 (m.d 2 4) (by simp) with h9370 | h9370
                              · linarith only [h9370, hlam, p9354_0]
                              · rcases p9354_3 (m.d 2 5) (by simp) with h9372 | h9372
                                · linarith only [h8663, h9372, hlam]
                                · linarith only [h9350, h9372, hlam]
                          · linarith only [h9257, h9367, hlam]
                        · linarith only [h9366, hlam, p9354_0]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        rcases p9354_3 (m.d 0 2) (by simp) with h9377 | h9377
                        · rcases p9354_3 (m.d 1 2) (by simp) with h9378 | h9378
                          · rcases p9354_3 (m.d 2 3) (by simp) with h9379 | h9379
                            · linarith only [h8661, h9379, hlam]
                            · rcases p9354_3 (m.d 2 4) (by simp) with h9381 | h9381
                              · linarith only [h8662, h9381, hlam]
                              · rcases p9354_3 (m.d 2 5) (by simp) with h9383 | h9383
                                · linarith only [h9383, hlam, p9354_0]
                                · rcases h3bigk with h9385c | h9385c | h9385c | h9385c | h9385c | h9385c | h9385c | h9385c | h9385c | h9385c | h9385c | h9385c | h9385c | h9385c | h9385c | h9385c | h9385c | h9385c | h9385c | h9385c | h9385c | h9385c | h9385c | h9385c | h9385c
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    linarith only [hlam, p9385_0]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    linarith only [h5135, hlam, p9385_1]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    rcases p9385_3 (m.d 0 3) (by simp) with h9388 | h9388
                                    · rcases p9385_3 (m.d 1 3) (by simp) with h9389 | h9389
                                      · rcases p9385_3 (m.d 2 3) (by simp) with h9390 | h9390
                                        · linarith only [h8661, h9390, hlam]
                                        · rcases p9385_3 (m.d 3 4) (by simp) with h9392 | h9392
                                          · linarith only [h8664, h9392, hlam]
                                          · linarith only [h9262, h9392, hlam]
                                      · linarith only [h9256, h9389, hlam]
                                    · linarith only [h8661, h9388, hlam]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    rcases p9385_3 (m.d 0 3) (by simp) with h9397 | h9397
                                    · rcases p9385_3 (m.d 1 3) (by simp) with h9398 | h9398
                                      · rcases p9385_3 (m.d 2 3) (by simp) with h9399 | h9399
                                        · linarith only [h8661, h9399, hlam]
                                        · rcases p9385_3 (m.d 3 4) (by simp) with h9401 | h9401
                                          · linarith only [h9401, hlam, p9385_0]
                                          · rcases p9385_3 (m.d 3 5) (by simp) with h9403 | h9403
                                            · linarith only [h8665, h9403, hlam]
                                            · linarith only [h9352, h9403, hlam]
                                      · linarith only [h9259, h9398, hlam]
                                    · linarith only [h9397, hlam, p9385_0]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    rcases p9385_3 (m.d 0 3) (by simp) with h9408 | h9408
                                    · rcases p9385_3 (m.d 1 3) (by simp) with h9409 | h9409
                                      · rcases p9385_3 (m.d 2 3) (by simp) with h9410 | h9410
                                        · linarith only [h8661, h9410, hlam]
                                        · rcases p9385_3 (m.d 3 4) (by simp) with h9412 | h9412
                                          · linarith only [h8664, h9412, hlam]
                                          · rcases p9385_3 (m.d 3 5) (by simp) with h9414 | h9414
                                            · linarith only [h9414, hlam, p9385_0]
                                            · rcases h5bigk with h9416c | h9416c | h9416c | h9416c | h9416c | h9416c | h9416c | h9416c | h9416c | h9416c | h9416c | h9416c | h9416c | h9416c | h9416c | h9416c | h9416c | h9416c | h9416c | h9416c | h9416c | h9416c | h9416c | h9416c | h9416c
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [hlam, p9416_0]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [h7870, hlam, p9416_1]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                rcases p9416_3 (m.d 0 5) (by simp) with h9419 | h9419
                                                · rcases p9416_3 (m.d 1 5) (by simp) with h9420 | h9420
                                                  · rcases p9416_3 (m.d 2 5) (by simp) with h9421 | h9421
                                                    · linarith only [h8663, h9421, hlam]
                                                    · rcases p9416_3 (m.d 3 5) (by simp) with h9423 | h9423
                                                      · linarith only [h8665, h9423, hlam]
                                                      · linarith only [h9348, h9423, hlam]
                                                  · linarith only [h9258, h9420, hlam]
                                                · linarith only [h8663, h9419, hlam]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [h8666, h9262, h9352, hc23, hc45, hlam, hphi, ht34, p9416_1]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [h8666, hlam, p9416_0]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                rcases p9416_3 (m.d 0 5) (by simp) with h9430 | h9430
                                                · linarith only [h7870, h9430, hlam]
                                                · rcases p9416_3 (m.d 1 5) (by simp) with h9432 | h9432
                                                  · rcases p9416_3 (m.d 2 5) (by simp) with h9433 | h9433
                                                    · linarith only [h9258, h9433, hlam]
                                                    · rcases p9416_3 (m.d 3 5) (by simp) with h9435 | h9435
                                                      · linarith only [h9260, h9435, hlam]
                                                      · rcases p9416_3 (m.d 4 5) (by simp) with h9437 | h9437
                                                        · linarith only [h9261, h9437, hlam]
                                                        · linarith only [h8666, h9437, hlam]
                                                  · linarith only [h7870, h9432, hlam]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [hlam, p9416_0]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                rcases p9416_3 (m.d 0 5) (by simp) with h9442 | h9442
                                                · linarith only [h7870, h9442, hlam]
                                                · linarith only [h8663, h9442, hlam]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                rcases p9416_3 (m.d 0 5) (by simp) with h9445 | h9445
                                                · linarith only [h7870, h9445, hlam]
                                                · linarith only [h8665, h9445, hlam]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [h8664, h8666, h9256, h9259, h9261, h9262, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9416_1]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [h8663, hlam, p9416_1]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [h9258, hlam, p9416_1]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [hlam, p9416_0]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [h9348, hlam, p9416_1]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [h9350, hlam, p9416_0]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [h8665, hlam, p9416_1]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [h9260, hlam, p9416_1]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [hc03, hc25, hlam, hphi, ht0b, ht5b, p9385_1, p9416_1]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [hlam, p9416_0]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [h9352, hlam, p9416_0]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [h8664, h8666, h9262, hc23, hc45, hlam, hphi, ht34, p9416_1]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [h9261, hlam, p9416_1]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                rcases p9416_3 (m.d 0 5) (by simp) with h9461 | h9461
                                                · linarith only [h8666, h9461, hlam]
                                                · linarith only [h8663, h9461, hlam]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [h9256, h9259, h9261, h9348, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9416_1]
                                              · have p9416_0 := h9416c.1
                                                have p9416_1 := h9416c.2.1
                                                have p9416_2 := h9416c.2.2.1
                                                have p9416_3 := h9416c.2.2.2
                                                linarith only [hlam, p9416_0]
                                      · linarith only [h9260, h9409, hlam]
                                    · linarith only [h9408, hlam, p9385_0]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    linarith only [h8664, h9256, h9262, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9385_1]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    linarith only [hlam, p9385_0]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    linarith only [h8664, h8666, h9259, h9261, h9262, hlam, p9385_2]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    rcases p9385_3 (m.d 0 3) (by simp) with h9471 | h9471
                                    · linarith only [h5135, h9471, hlam]
                                    · linarith only [h8664, h9471, hlam]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    rcases p9385_3 (m.d 0 3) (by simp) with h9474 | h9474
                                    · linarith only [h5135, h9474, hlam]
                                    · linarith only [h8665, h9474, hlam]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    linarith only [h8661, hlam, p9385_1]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    linarith only [h9256, hlam, p9385_1]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    linarith only [hlam, p9385_0]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    linarith only [h9262, hlam, p9385_0]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    linarith only [h9348, hlam, p9385_0]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    linarith only [h8664, hlam, p9385_0]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    linarith only [h9259, hlam, p9385_0]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    linarith only [h8664, h8666, h9259, h9261, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9385_1]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    linarith only [hlam, p9385_0]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    linarith only [h9352, hlam, p9385_0]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    linarith only [h8665, hlam, p9385_0]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    linarith only [h9260, hlam, p9385_0]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    rcases p9385_3 (m.d 0 3) (by simp) with h9489 | h9489
                                    · rcases p9385_3 (m.d 1 3) (by simp) with h9490 | h9490
                                      · rcases p9385_3 (m.d 2 3) (by simp) with h9491 | h9491
                                        · linarith only [h9491, hlam, p9385_0]
                                        · rcases p9385_3 (m.d 3 4) (by simp) with h9493 | h9493
                                          · linarith only [h9352, h9493, hlam]
                                          · linarith only [h9262, h9493, hlam]
                                      · linarith only [h9256, h9490, hlam]
                                    · linarith only [h8661, h9489, hlam]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    linarith only [h8665, h9262, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9385_1]
                                  · have p9385_0 := h9385c.1
                                    have p9385_1 := h9385c.2.1
                                    have p9385_2 := h9385c.2.2.1
                                    have p9385_3 := h9385c.2.2.2
                                    linarith only [hlam, p9385_0]
                          · linarith only [h9258, h9378, hlam]
                        · linarith only [h9377, hlam, p9354_0]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p9354_1]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        linarith only [hlam, p9354_0]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        rcases p9354_3 (m.d 0 2) (by simp) with h9504 | h9504
                        · linarith only [h0, h9504, hlam]
                        · linarith only [h8661, h9504, hlam]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        rcases p9354_3 (m.d 0 2) (by simp) with h9507 | h9507
                        · linarith only [h0, h9507, hlam]
                        · linarith only [h8662, h9507, hlam]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        rcases p9354_3 (m.d 0 2) (by simp) with h9510 | h9510
                        · linarith only [h0, h9510, hlam]
                        · linarith only [h8663, h9510, hlam]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        linarith only [h8661, hlam, p9354_0]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        linarith only [h9256, hlam, p9354_0]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        linarith only [hlam, p9354_0]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        linarith only [h9262, hlam, p9354_1]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        linarith only [h9348, hlam, p9354_1]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        linarith only [h8662, hlam, p9354_0]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        linarith only [h9257, hlam, p9354_0]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        linarith only [h8662, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9354_1]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        linarith only [hlam, p9354_0]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        linarith only [h9350, hlam, p9354_0]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        linarith only [h8663, hlam, p9354_0]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        linarith only [h9258, hlam, p9354_0]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        linarith only [h0, h8663, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9354_1]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        linarith only [h8665, h8666, h9256, h9259, h9261, h9348, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9354_1]
                      · have p9354_0 := h9354c.1
                        have p9354_1 := h9354c.2.1
                        have p9354_2 := h9354c.2.2.1
                        have p9354_3 := h9354c.2.2.2
                        linarith only [hlam, p9354_0]
            · rcases m.htr 2 3 4 (by decide) (by decide) with h9528 | h9528
              · rcases m.htr 2 3 5 (by decide) (by decide) with h9529 | h9529
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9530 | h9530
                  · linarith only [h6923, h9261, h9530, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9532 | h9532
                    · linarith only [h6923, h9261, h9528, h9532, hc01, hc23, hlam, hphi, ht12]
                    · rcases h2bigk with h9534c | h9534c | h9534c | h9534c | h9534c | h9534c | h9534c | h9534c | h9534c | h9534c | h9534c | h9534c | h9534c | h9534c | h9534c | h9534c | h9534c | h9534c | h9534c | h9534c | h9534c | h9534c | h9534c | h9534c | h9534c
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [hlam, p9534_0]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [h0, hlam, p9534_0]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [h0, h9529, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p9534_1]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        rcases p9534_3 (m.d 0 2) (by simp) with h9538 | h9538
                        · rcases p9534_3 (m.d 1 2) (by simp) with h9539 | h9539
                          · rcases p9534_3 (m.d 2 3) (by simp) with h9540 | h9540
                            · linarith only [h8661, h9540, hlam]
                            · linarith only [h9528, h9540, hlam]
                          · linarith only [h9257, h9539, hlam]
                        · linarith only [h9538, hlam, p9534_0]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        rcases p9534_3 (m.d 0 2) (by simp) with h9545 | h9545
                        · rcases p9534_3 (m.d 1 2) (by simp) with h9546 | h9546
                          · rcases p9534_3 (m.d 2 3) (by simp) with h9547 | h9547
                            · linarith only [h8661, h9547, hlam]
                            · linarith only [h9529, h9547, hlam]
                          · linarith only [h9258, h9546, hlam]
                        · linarith only [h9545, hlam, p9534_0]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p9534_1]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [hlam, p9534_0]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [h9529, h9532, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9534_1]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        rcases p9534_3 (m.d 0 2) (by simp) with h9555 | h9555
                        · linarith only [h0, h9555, hlam]
                        · linarith only [h8662, h9555, hlam]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        rcases p9534_3 (m.d 0 2) (by simp) with h9558 | h9558
                        · linarith only [h0, h9558, hlam]
                        · linarith only [h8663, h9558, hlam]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [h8661, hlam, p9534_0]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [h9256, hlam, p9534_0]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [hlam, p9534_0]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [h8661, h9528, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p9534_1]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [h0, h8661, h9528, h9530, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9534_1]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [h8662, hlam, p9534_0]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [h9257, hlam, p9534_0]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [h9528, hlam, p9534_0]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [hlam, p9534_0]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [h9530, hlam, p9534_0]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [h8663, hlam, p9534_0]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [h9258, hlam, p9534_0]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [h9529, hlam, p9534_0]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [h0, h8663, h9528, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9534_1]
                      · have p9534_0 := h9534c.1
                        have p9534_1 := h9534c.2.1
                        have p9534_2 := h9534c.2.2.1
                        have p9534_3 := h9534c.2.2.2
                        linarith only [hlam, p9534_0]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9576 | h9576
                  · linarith only [h6923, h9261, h9576, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9578 | h9578
                    · linarith only [h6923, h9261, h9578, hc01, hc34, hlam, hphi, ht12, ht23]
                    · rcases h2bigk with h9580c | h9580c | h9580c | h9580c | h9580c | h9580c | h9580c | h9580c | h9580c | h9580c | h9580c | h9580c | h9580c | h9580c | h9580c | h9580c | h9580c | h9580c | h9580c | h9580c | h9580c | h9580c | h9580c | h9580c | h9580c
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [hlam, p9580_0]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [h0, hlam, p9580_0]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [h0, h9528, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9580_1]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        rcases p9580_3 (m.d 0 2) (by simp) with h9584 | h9584
                        · rcases p9580_3 (m.d 1 2) (by simp) with h9585 | h9585
                          · rcases p9580_3 (m.d 2 3) (by simp) with h9586 | h9586
                            · linarith only [h8661, h9586, hlam]
                            · linarith only [h9528, h9586, hlam]
                          · linarith only [h9257, h9585, hlam]
                        · linarith only [h9584, hlam, p9580_0]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [h0, h9528, h9529, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9580_1]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p9580_1]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [hlam, p9580_0]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [h9528, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9580_1]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        rcases p9580_3 (m.d 0 2) (by simp) with h9595 | h9595
                        · linarith only [h0, h9595, hlam]
                        · linarith only [h8662, h9595, hlam]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [h9528, h9529, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9580_1]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [h8661, hlam, p9580_0]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [h9256, hlam, p9580_0]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [hlam, p9580_0]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [h8661, h9528, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p9580_1]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [h9529, hlam, p9580_1]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [h8662, hlam, p9580_0]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [h9257, hlam, p9580_0]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [h9528, hlam, p9580_0]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [hlam, p9580_0]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [h9576, hlam, p9580_0]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [h8663, hlam, p9580_0]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [h9258, hlam, p9580_0]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [h0, h8663, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9580_1]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [h5135, h8665, h9256, h9528, h9529, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9580_1]
                      · have p9580_0 := h9580c.1
                        have p9580_1 := h9580c.2.1
                        have p9580_2 := h9580c.2.2.1
                        have p9580_3 := h9580c.2.2.2
                        linarith only [hlam, p9580_0]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h9614 | h9614
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9615 | h9615
                  · linarith only [h6923, h8664, h9261, h9528, h9614, h9615, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                  · linarith only [h9528, h9614, h9615, hlam]
                · rcases m.htr 2 4 5 (by decide) (by decide) with h9618 | h9618
                  · linarith only [h6923, h9261, h9618, hc01, hc24, hlam, hphi, ht12]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h9620 | h9620
                    · linarith only [h6923, h8664, h9261, h9620, hlam]
                    · rcases h2bigk with h9622c | h9622c | h9622c | h9622c | h9622c | h9622c | h9622c | h9622c | h9622c | h9622c | h9622c | h9622c | h9622c | h9622c | h9622c | h9622c | h9622c | h9622c | h9622c | h9622c | h9622c | h9622c | h9622c | h9622c | h9622c
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        linarith only [hlam, p9622_0]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        linarith only [h0, hlam, p9622_0]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        rcases p9622_3 (m.d 0 2) (by simp) with h9625 | h9625
                        · rcases p9622_3 (m.d 1 2) (by simp) with h9626 | h9626
                          · rcases p9622_3 (m.d 2 3) (by simp) with h9627 | h9627
                            · linarith only [h9627, hlam, p9622_0]
                            · rcases p9622_3 (m.d 2 4) (by simp) with h9629 | h9629
                              · linarith only [h8662, h9629, hlam]
                              · linarith only [h9528, h9629, hlam]
                          · linarith only [h9256, h9626, hlam]
                        · linarith only [h9625, hlam, p9622_0]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        rcases p9622_3 (m.d 0 2) (by simp) with h9634 | h9634
                        · rcases p9622_3 (m.d 1 2) (by simp) with h9635 | h9635
                          · rcases p9622_3 (m.d 2 3) (by simp) with h9636 | h9636
                            · linarith only [h8661, h9636, hlam]
                            · rcases p9622_3 (m.d 2 4) (by simp) with h9638 | h9638
                              · linarith only [h9638, hlam, p9622_0]
                              · rcases p9622_3 (m.d 2 5) (by simp) with h9640 | h9640
                                · linarith only [h8663, h9640, hlam]
                                · linarith only [h9618, h9640, hlam]
                          · linarith only [h9257, h9635, hlam]
                        · linarith only [h9634, hlam, p9622_0]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        rcases p9622_3 (m.d 0 2) (by simp) with h9645 | h9645
                        · rcases p9622_3 (m.d 1 2) (by simp) with h9646 | h9646
                          · rcases p9622_3 (m.d 2 3) (by simp) with h9647 | h9647
                            · linarith only [h8661, h9647, hlam]
                            · rcases p9622_3 (m.d 2 4) (by simp) with h9649 | h9649
                              · linarith only [h8662, h9649, hlam]
                              · rcases p9622_3 (m.d 2 5) (by simp) with h9651 | h9651
                                · linarith only [h9651, hlam, p9622_0]
                                · rcases h3bigk with h9653c | h9653c | h9653c | h9653c | h9653c | h9653c | h9653c | h9653c | h9653c | h9653c | h9653c | h9653c | h9653c | h9653c | h9653c | h9653c | h9653c | h9653c | h9653c | h9653c | h9653c | h9653c | h9653c | h9653c | h9653c
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    linarith only [hlam, p9653_0]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    linarith only [h5135, hlam, p9653_1]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    rcases p9653_3 (m.d 0 3) (by simp) with h9656 | h9656
                                    · rcases p9653_3 (m.d 1 3) (by simp) with h9657 | h9657
                                      · rcases p9653_3 (m.d 2 3) (by simp) with h9658 | h9658
                                        · linarith only [h8661, h9658, hlam]
                                        · rcases p9653_3 (m.d 3 4) (by simp) with h9660 | h9660
                                          · linarith only [h8664, h9660, hlam]
                                          · linarith only [h9528, h9660, hlam]
                                      · linarith only [h9256, h9657, hlam]
                                    · linarith only [h8661, h9656, hlam]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    rcases p9653_3 (m.d 0 3) (by simp) with h9665 | h9665
                                    · rcases p9653_3 (m.d 1 3) (by simp) with h9666 | h9666
                                      · rcases p9653_3 (m.d 2 3) (by simp) with h9667 | h9667
                                        · linarith only [h8661, h9667, hlam]
                                        · rcases p9653_3 (m.d 3 4) (by simp) with h9669 | h9669
                                          · linarith only [h9669, hlam, p9653_0]
                                          · rcases p9653_3 (m.d 3 5) (by simp) with h9671 | h9671
                                            · linarith only [h8665, h9671, hlam]
                                            · linarith only [h9620, h9671, hlam]
                                      · linarith only [h9259, h9666, hlam]
                                    · linarith only [h9665, hlam, p9653_0]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    rcases p9653_3 (m.d 0 3) (by simp) with h9676 | h9676
                                    · rcases p9653_3 (m.d 1 3) (by simp) with h9677 | h9677
                                      · rcases p9653_3 (m.d 2 3) (by simp) with h9678 | h9678
                                        · linarith only [h8661, h9678, hlam]
                                        · rcases p9653_3 (m.d 3 4) (by simp) with h9680 | h9680
                                          · linarith only [h8664, h9680, hlam]
                                          · rcases p9653_3 (m.d 3 5) (by simp) with h9682 | h9682
                                            · linarith only [h9682, hlam, p9653_0]
                                            · rcases h5bigk with h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c | h9684c
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [hlam, p9684_0]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [h7870, hlam, p9684_1]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                rcases p9684_3 (m.d 0 5) (by simp) with h9687 | h9687
                                                · rcases p9684_3 (m.d 1 5) (by simp) with h9688 | h9688
                                                  · rcases p9684_3 (m.d 2 5) (by simp) with h9689 | h9689
                                                    · linarith only [h8663, h9689, hlam]
                                                    · rcases p9684_3 (m.d 3 5) (by simp) with h9691 | h9691
                                                      · linarith only [h8665, h9691, hlam]
                                                      · linarith only [h9614, h9691, hlam]
                                                  · linarith only [h9258, h9688, hlam]
                                                · linarith only [h8663, h9687, hlam]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [h7870, h9261, h9528, h9620, hc23, hc45, hlam, hphi, ht34, p9684_1]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [h8666, hlam, p9684_0]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [h8665, h9261, h9528, h9620, hc23, hc45, hlam, hphi, ht34, p9684_1]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [hlam, p9684_0]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                rcases p9684_3 (m.d 0 5) (by simp) with h9700 | h9700
                                                · linarith only [h7870, h9700, hlam]
                                                · linarith only [h8663, h9700, hlam]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [h9261, h9528, h9620, hc23, hc45, hlam, hphi, ht34, p9684_1]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [h9261, hlam, p9684_0]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [h8663, hlam, p9684_1]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [h9258, hlam, p9684_1]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [hlam, p9684_0]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [h9614, hlam, p9684_1]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [h9618, hlam, p9684_0]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [h8665, hlam, p9684_1]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [h9260, hlam, p9684_1]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [h0, h8661, h9618, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9653_1, p9684_1]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [hlam, p9684_0]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [h9620, hlam, p9684_0]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [h8664, h8666, h9528, hc23, hc45, hlam, hphi, ht34, p9684_1]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [h7870, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p9684_1]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                rcases p9684_3 (m.d 0 5) (by simp) with h9717 | h9717
                                                · linarith only [h8666, h9717, hlam]
                                                · linarith only [h8663, h9717, hlam]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [h9614, hc23, hc45, hlam, hphi, ht34, p9684_1]
                                              · have p9684_0 := h9684c.1
                                                have p9684_1 := h9684c.2.1
                                                have p9684_2 := h9684c.2.2.1
                                                have p9684_3 := h9684c.2.2.2
                                                linarith only [hlam, p9684_0]
                                      · linarith only [h9260, h9677, hlam]
                                    · linarith only [h9676, hlam, p9653_0]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    linarith only [h8664, h9528, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9653_1]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    linarith only [hlam, p9653_0]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    rcases p9653_3 (m.d 0 3) (by simp) with h9726 | h9726
                                    · linarith only [h5135, h9726, hlam]
                                    · linarith only [h8661, h9726, hlam]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    rcases p9653_3 (m.d 0 3) (by simp) with h9729 | h9729
                                    · linarith only [h5135, h9729, hlam]
                                    · linarith only [h8664, h9729, hlam]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    rcases p9653_3 (m.d 0 3) (by simp) with h9732 | h9732
                                    · linarith only [h5135, h9732, hlam]
                                    · linarith only [h8665, h9732, hlam]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    linarith only [h8661, hlam, p9653_1]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    linarith only [h9256, hlam, p9653_1]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    linarith only [hlam, p9653_0]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    linarith only [h9528, hlam, p9653_0]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    linarith only [h9614, hlam, p9653_0]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    linarith only [h8664, hlam, p9653_0]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    linarith only [h9259, hlam, p9653_0]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    linarith only [h8664, h8666, hc23, hc45, hlam, hphi, ht34, p9653_1]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    linarith only [hlam, p9653_0]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    linarith only [h9620, hlam, p9653_0]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    linarith only [h8665, hlam, p9653_0]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    linarith only [h9260, hlam, p9653_0]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    rcases p9653_3 (m.d 0 3) (by simp) with h9747 | h9747
                                    · rcases p9653_3 (m.d 1 3) (by simp) with h9748 | h9748
                                      · rcases p9653_3 (m.d 2 3) (by simp) with h9749 | h9749
                                        · linarith only [h9749, hlam, p9653_0]
                                        · rcases p9653_3 (m.d 3 4) (by simp) with h9751 | h9751
                                          · linarith only [h9620, h9751, hlam]
                                          · linarith only [h9528, h9751, hlam]
                                      · linarith only [h9256, h9748, hlam]
                                    · linarith only [h8661, h9747, hlam]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    linarith only [h8665, h9528, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9653_1]
                                  · have p9653_0 := h9653c.1
                                    have p9653_1 := h9653c.2.1
                                    have p9653_2 := h9653c.2.2.1
                                    have p9653_3 := h9653c.2.2.2
                                    linarith only [hlam, p9653_0]
                          · linarith only [h9258, h9646, hlam]
                        · linarith only [h9645, hlam, p9622_0]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        linarith only [h0, hc01, hc12, hlam, hphi, p9622_1]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        linarith only [hlam, p9622_0]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        rcases p9622_3 (m.d 0 2) (by simp) with h9762 | h9762
                        · linarith only [h0, h9762, hlam]
                        · linarith only [h8661, h9762, hlam]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        rcases p9622_3 (m.d 0 2) (by simp) with h9765 | h9765
                        · linarith only [h0, h9765, hlam]
                        · linarith only [h8662, h9765, hlam]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        rcases p9622_3 (m.d 0 2) (by simp) with h9768 | h9768
                        · linarith only [h0, h9768, hlam]
                        · linarith only [h8663, h9768, hlam]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        linarith only [h8661, hlam, p9622_0]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        linarith only [h9256, hlam, p9622_0]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        linarith only [hlam, p9622_0]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        linarith only [h9528, hlam, p9622_1]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        linarith only [h9614, hlam, p9622_1]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        linarith only [h8662, hlam, p9622_0]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        linarith only [h9257, hlam, p9622_0]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        linarith only [h8662, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9622_1]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        linarith only [hlam, p9622_0]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        linarith only [h9618, hlam, p9622_0]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        linarith only [h8663, hlam, p9622_0]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        linarith only [h9258, hlam, p9622_0]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        linarith only [h0, h8663, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p9622_1]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        linarith only [h5135, h8665, h9256, h9614, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p9622_1]
                      · have p9622_0 := h9622c.1
                        have p9622_1 := h9622c.2.1
                        have p9622_2 := h9622c.2.2.1
                        have p9622_3 := h9622c.2.2.2
                        linarith only [hlam, p9622_0]
          · linarith only [h5135, h8665, h9260, hlam]
        · linarith only [h5135, h8664, h9259, hlam]
      · linarith only [h0, h8663, h9258, hlam]
    · linarith only [h0, h8662, h9257, hlam]
  · linarith only [h0, h8661, h9256, hlam]

set_option maxHeartbeats 7524000 in
set_option maxHeartbeats 7524000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6923 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7870 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8661 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8662 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8663 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8664 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8665 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  have h6923 := hg6923
  have h7870 := hg7870
  rcases m.htr 0 4 5 (by decide) (by decide) with h8666 | h8666
  · exact r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x0_x0_x0_x0_x0 m hb2 hb3 hb5 hg0 hg5135 hg6923 hg7870 h8661 h8662 h8663 h8664 h8665 h8666
  · exact r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x0_x0_x0_x0_x1 m hb2 hb3 hb5 hg0 hg5135 hg6923 hg7870 h8661 h8662 h8663 h8664 h8665 h8666

set_option maxHeartbeats 7524000 in
set_option maxHeartbeats 7524000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x0_x0_x0_x1 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6923 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7870 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8661 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8662 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8663 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8664 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h8665 : (m.d 3 5 + m.lam ≤ m.d 0 3 ∧ m.d 3 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 3))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  have h6923 := hg6923
  have h7870 := hg7870
  rcases m.htr 0 4 5 (by decide) (by decide) with h9791 | h9791
  · linarith only [h8664, h8665, h9791, hlam]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h9793 | h9793
    · rcases m.htr 1 2 4 (by decide) (by decide) with h9794 | h9794
      · rcases m.htr 1 2 5 (by decide) (by decide) with h9795 | h9795
        · rcases m.htr 1 3 4 (by decide) (by decide) with h9796 | h9796
          · rcases m.htr 1 3 5 (by decide) (by decide) with h9797 | h9797
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9798 | h9798
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9799 | h9799
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9800 | h9800
                  · linarith only [h0, h5135, h8661, h8665, h9800, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9802 | h9802
                    · linarith only [h8661, h8665, h9791, h9797, h9799, h9802, hc04, hc13, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9804 | h9804
                      · linarith only [h6923, h8661, h8665, h9791, h9793, h9797, h9799, h9804, hc01, hc12, hlam, hphi]
                      · rcases h2bigk with h9806c | h9806c | h9806c | h9806c | h9806c | h9806c | h9806c | h9806c | h9806c | h9806c | h9806c | h9806c | h9806c | h9806c | h9806c | h9806c | h9806c | h9806c | h9806c | h9806c | h9806c | h9806c | h9806c | h9806c | h9806c
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [hlam, p9806_0]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [h0, hlam, p9806_0]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [h0, h9799, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9806_1]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          rcases p9806_3 (m.d 0 2) (by simp) with h9810 | h9810
                          · rcases p9806_3 (m.d 1 2) (by simp) with h9811 | h9811
                            · rcases p9806_3 (m.d 2 3) (by simp) with h9812 | h9812
                              · linarith only [h8661, h9812, hlam]
                              · linarith only [h9799, h9812, hlam]
                            · linarith only [h9794, h9811, hlam]
                          · linarith only [h9810, hlam, p9806_0]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [h0, h9799, h9800, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9806_1]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9806_1]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [hlam, p9806_0]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [h9799, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9806_1]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          rcases p9806_3 (m.d 0 2) (by simp) with h9821 | h9821
                          · linarith only [h0, h9821, hlam]
                          · linarith only [h8662, h9821, hlam]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [h9799, h9800, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9806_1]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [h8661, hlam, p9806_0]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [h9793, hlam, p9806_0]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [hlam, p9806_0]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [h8663, h9799, h9800, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p9806_1]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [h9800, hlam, p9806_1]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [h8662, hlam, p9806_0]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [h9794, hlam, p9806_0]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [h9799, hlam, p9806_0]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [hlam, p9806_0]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [h9802, hlam, p9806_0]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [h8663, hlam, p9806_0]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [h9795, hlam, p9806_0]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [h8663, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9806_1]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [h8663, h8665, h9793, h9796, h9798, h9799, h9804, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9806_1]
                        · have p9806_0 := h9806c.1
                          have p9806_1 := h9806c.2.1
                          have p9806_2 := h9806c.2.2.1
                          have p9806_3 := h9806c.2.2.2
                          linarith only [hlam, p9806_0]
                · linarith only [h8664, h8665, h9799, hc23, hc35, hlam, hphi]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9841 | h9841
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9842 | h9842
                  · linarith only [h0, h5135, h8661, h8665, h9842, hc01, hc12, hlam, hphi]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9844 | h9844
                    · linarith only [h6923, h9798, h9844, hc01, hc24, hlam, hphi, ht12]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9846 | h9846
                      · linarith only [h6923, h9798, h9846, hc01, hc34, hlam, hphi, ht12, ht23]
                      · rcases h2bigk with h9848c | h9848c | h9848c | h9848c | h9848c | h9848c | h9848c | h9848c | h9848c | h9848c | h9848c | h9848c | h9848c | h9848c | h9848c | h9848c | h9848c | h9848c | h9848c | h9848c | h9848c | h9848c | h9848c | h9848c | h9848c
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [hlam, p9848_0]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [h0, hlam, p9848_0]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [h0, h9841, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9848_1]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          rcases p9848_3 (m.d 0 2) (by simp) with h9852 | h9852
                          · rcases p9848_3 (m.d 1 2) (by simp) with h9853 | h9853
                            · rcases p9848_3 (m.d 2 3) (by simp) with h9854 | h9854
                              · linarith only [h8661, h9854, hlam]
                              · linarith only [h9841, h9854, hlam]
                            · linarith only [h9794, h9853, hlam]
                          · linarith only [h9852, hlam, p9848_0]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [h0, h9841, h9842, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9848_1]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9848_1]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [hlam, p9848_0]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [h9841, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9848_1]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          rcases p9848_3 (m.d 0 2) (by simp) with h9863 | h9863
                          · linarith only [h0, h9863, hlam]
                          · linarith only [h8662, h9863, hlam]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [h9841, h9842, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9848_1]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [h8661, hlam, p9848_0]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [h9793, hlam, p9848_0]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [hlam, p9848_0]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [h8663, h9841, h9842, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p9848_1]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [h9842, hlam, p9848_1]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [h8662, hlam, p9848_0]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [h9794, hlam, p9848_0]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [h9841, hlam, p9848_0]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [hlam, p9848_0]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [h9844, hlam, p9848_0]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [h8663, hlam, p9848_0]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [h9795, hlam, p9848_0]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [h8663, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9848_1]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [h8663, h8665, h9793, h9797, h9841, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9848_1]
                        · have p9848_0 := h9848c.1
                          have p9848_1 := h9848c.2.1
                          have p9848_2 := h9848c.2.2.1
                          have p9848_3 := h9848c.2.2.2
                          linarith only [hlam, p9848_0]
                · linarith only [h8664, h8665, h9793, h9797, h9841, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h9883 | h9883
              · linarith only [h6923, h9791, h9796, h9797, h9883, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h9885 | h9885
                · rcases m.htr 2 3 5 (by decide) (by decide) with h9886 | h9886
                  · linarith only [h5135, h9797, h9886, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h9888 | h9888
                    · linarith only [h0, h7870, h8662, h9883, h9888, hc01, hc12, hlam, hphi]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h9890 | h9890
                      · linarith only [h6923, h9883, h9885, h9890, hc01, hc23, hlam, hphi, ht12]
                      · rcases h2bigk with h9892c | h9892c | h9892c | h9892c | h9892c | h9892c | h9892c | h9892c | h9892c | h9892c | h9892c | h9892c | h9892c | h9892c | h9892c | h9892c | h9892c | h9892c | h9892c | h9892c | h9892c | h9892c | h9892c | h9892c | h9892c
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [hlam, p9892_0]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [h0, hlam, p9892_0]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [h0, h9885, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9892_1]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          rcases p9892_3 (m.d 0 2) (by simp) with h9896 | h9896
                          · rcases p9892_3 (m.d 1 2) (by simp) with h9897 | h9897
                            · rcases p9892_3 (m.d 2 3) (by simp) with h9898 | h9898
                              · linarith only [h8661, h9898, hlam]
                              · linarith only [h9885, h9898, hlam]
                            · linarith only [h9794, h9897, hlam]
                          · linarith only [h9896, hlam, p9892_0]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [h0, h9885, h9886, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9892_1]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [h0, hc01, hc12, hlam, hphi, p9892_1]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [hlam, p9892_0]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [h9885, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9892_1]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          rcases p9892_3 (m.d 0 2) (by simp) with h9907 | h9907
                          · linarith only [h0, h9907, hlam]
                          · linarith only [h8662, h9907, hlam]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [h9885, h9886, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9892_1]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [h8661, hlam, p9892_0]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [h9793, hlam, p9892_0]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [hlam, p9892_0]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [h8663, h9885, h9886, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p9892_1]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [h9886, hlam, p9892_1]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [h8662, hlam, p9892_0]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [h9794, hlam, p9892_0]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [h9885, hlam, p9892_0]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [hlam, p9892_0]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [h9888, hlam, p9892_0]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [h8663, hlam, p9892_0]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [h9795, hlam, p9892_0]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [h8663, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p9892_1]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [h0, h8663, h9885, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p9892_1]
                        · have p9892_0 := h9892c.1
                          have p9892_1 := h9892c.2.1
                          have p9892_2 := h9892c.2.2.1
                          have p9892_3 := h9892c.2.2.2
                          linarith only [hlam, p9892_0]
                · linarith only [h8664, h8665, h9885, hc23, hc35, hlam, hphi]
          · linarith only [h5135, h8664, h9796, hlam]
        · linarith only [h0, h8663, h9795, hlam]
      · linarith only [h0, h8662, h9794, hlam]
    · linarith only [h0, h8661, h9793, hlam]

set_option maxHeartbeats 7524000 in
set_option maxHeartbeats 7524000 in
theorem r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x0_x0_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg5135 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg6923 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg7870 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h8661 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h8662 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h8663 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h8664 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
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
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have h0 := hg0
  have h5135 := hg5135
  have h6923 := hg6923
  have h7870 := hg7870
  rcases m.htr 0 3 5 (by decide) (by decide) with h8665 | h8665
  · exact r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x0_x0_x0_x0 m hb2 hb3 hb5 hg0 hg5135 hg6923 hg7870 h8661 h8662 h8663 h8664 h8665
  · exact r1l7_22_13_15_H_I_L_I_L_I_s8_x0_x0_x0_x0_x1 m hb2 hb3 hb5 hg0 hg5135 hg6923 hg7870 h8661 h8662 h8663 h8664 h8665

end R2N4
