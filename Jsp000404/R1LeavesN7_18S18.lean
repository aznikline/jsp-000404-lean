import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_18S9
import Jsp000404.R1LeavesN7_18S16
import Jsp000404.R1LeavesN7_18S17

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9598000 in
set_option maxHeartbeats 9598000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s7_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5743 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h5744 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  have h0 := hg0
  rcases m.htr 0 1 5 (by decide) (by decide) with h6359 | h6359
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6360 | h6360
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6361 | h6361
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6362 | h6362
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6363 | h6363
          · linarith only [h5743, h5744, h6363, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6365 | h6365
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6366 | h6366
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6367 | h6367
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6368 | h6368
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6369 | h6369
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6370 | h6370
                      · linarith only [h5743, h5744, h6363, h6368, h6370, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6372 | h6372
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6373 | h6373
                          · linarith only [h5743, h5744, h6367, h6370, h6373, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6375 | h6375
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6376 | h6376
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6377 | h6377
                                · rcases h0bigk with h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c | h6378c
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [hlam, p6378_0]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [h0, hlam, p6378_1]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [h5744, h6370, hc03, hc34, hlam, hphi, p6378_1]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [h5744, hlam, p6378_1]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [h5744, h6370, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6378_1]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6378_1]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [hlam, p6378_0]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [h0, h6360, h6375, h6377, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6378_1]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [h0, h5744, hc01, hc12, hlam, hphi, p6378_1]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    rcases p6378_3 (m.d 0 1) (by simp) with h6388 | h6388
                                    · linarith only [h0, h6388, hlam]
                                    · linarith only [h6359, h6388, hlam]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [h5743, hlam, p6378_1]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [h6360, hlam, p6378_1]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [hlam, p6378_0]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [h6363, hlam, p6378_1]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [h5743, h5744, h6370, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p6378_1]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [h5743, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p6378_1]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [h6361, hlam, p6378_0]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [h5744, h6370, hc03, hc34, hlam, hphi, p6378_1]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [hlam, p6378_0]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    rcases p6378_3 (m.d 0 1) (by simp) with h6400 | h6400
                                    · linarith only [h5744, h6400, hlam]
                                    · linarith only [h6359, h6400, hlam]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [h6359, hlam, p6378_0]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [h6362, hlam, p6378_1]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [h6365, hlam, p6378_0]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [h6366, hlam, p6378_1]
                                  · have p6378_0 := h6378c.1
                                    have p6378_1 := h6378c.2.1
                                    have p6378_2 := h6378c.2.2.1
                                    have p6378_3 := h6378c.2.2.2
                                    linarith only [hlam, p6378_0]
                                · linarith only [h5743, h5744, h6370, h6377, hc13, hc45, hlam, hphi, ht34]
                              · linarith only [h6373, h6375, h6376, hlam]
                            · linarith only [h5743, h5744, h6365, h6370, h6375, hc23, hc34, hlam, hphi]
                        · linarith only [h5743, h5744, h6365, h6370, h6372, hc13, hc34, hlam, hphi]
                    · linarith only [h0, h6362, h6369, hlam]
                  · linarith only [h0, h5743, h6361, h6365, h6368, hc02, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h6360, h6367, hlam]
              · linarith only [h5743, h5744, h6365, h6366, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6416 | h6416
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6417 | h6417
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6418 | h6418
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6419 | h6419
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6420 | h6420
                      · linarith only [h5743, h5744, h6363, h6420, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6422 | h6422
                        · linarith only [h5743, h6365, h6422, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6424 | h6424
                          · linarith only [h0, h5744, h6360, h6420, h6424, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6426 | h6426
                            · linarith only [h5743, h6365, h6417, h6426, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6428 | h6428
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6429 | h6429
                                · rcases h0bigk with h6430c | h6430c | h6430c | h6430c | h6430c | h6430c | h6430c | h6430c | h6430c | h6430c | h6430c | h6430c | h6430c | h6430c | h6430c | h6430c | h6430c | h6430c | h6430c | h6430c | h6430c | h6430c | h6430c | h6430c | h6430c
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [hlam, p6430_0]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [h0, hlam, p6430_1]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [h5743, h5744, h6417, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6430_1]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [h5744, hlam, p6430_1]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [h5743, h5744, h6365, h6417, h6420, hc23, hc34, hlam, hphi, p6430_1]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6430_1]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [hlam, p6430_0]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    rcases p6430_3 (m.d 0 1) (by simp) with h6438 | h6438
                                    · linarith only [h0, h6438, hlam]
                                    · linarith only [h5743, h6438, hlam]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [h0, h5744, h6359, h6417, h6422, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6430_1]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    rcases p6430_3 (m.d 0 1) (by simp) with h6442 | h6442
                                    · linarith only [h0, h6442, hlam]
                                    · linarith only [h6359, h6442, hlam]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [h5743, hlam, p6430_1]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [h6360, hlam, p6430_1]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [hlam, p6430_0]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [h6363, hlam, p6430_1]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [h6365, hlam, p6430_1]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [h6359, h6417, h6422, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6430_1]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [h6361, hlam, p6430_0]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [h5743, h5744, h6417, h6420, hc23, hc34, hlam, hphi, p6430_1]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [hlam, p6430_0]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [h5743, h5744, h6365, h6417, h6420, hc23, hc34, hlam, hphi, p6430_1]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [h6359, hlam, p6430_0]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [h6362, hlam, p6430_1]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [h0, h5743, h6359, h6417, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6430_1]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [h6416, hlam, p6430_1]
                                  · have p6430_0 := h6430c.1
                                    have p6430_1 := h6430c.2.1
                                    have p6430_2 := h6430c.2.2.1
                                    have p6430_3 := h6430c.2.2.2
                                    linarith only [hlam, p6430_0]
                                · linarith only [h5743, h5744, h6417, h6420, h6429, hc23, hc45, hlam, hphi, ht34]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6461 | h6461
                                · rcases h0bigk with h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c | h6462c
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [hlam, p6462_0]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [h0, hlam, p6462_1]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [h5743, h5744, h6417, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6462_1]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [h5744, hlam, p6462_1]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [h5744, h6416, h6420, h6424, h6428, hc23, hc34, hlam, hphi, p6462_1]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6462_1]
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
                                    · linarith only [h5743, h6470, hlam]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [h0, h5744, h6359, h6419, h6424, h6428, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6462_1]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [h0, h6416, h6424, h6428, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6462_1]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [h5743, hlam, p6462_1]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [h6360, hlam, p6462_1]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [hlam, p6462_0]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [h6363, hlam, p6462_1]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [h6365, hlam, p6462_1]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [h6359, h6419, h6424, h6428, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6462_1]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [h6361, hlam, p6462_0]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [h5743, h5744, h6417, h6420, hc23, hc34, hlam, hphi, p6462_1]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [hlam, p6462_0]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [h5744, h6416, h6420, h6424, h6428, hc23, hc34, hlam, hphi, p6462_1]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [h6359, hlam, p6462_0]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [h6362, hlam, p6462_1]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [h5743, h6365, h6417, hc23, hc35, hlam, hphi, p6462_1]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [h6416, hlam, p6462_1]
                                  · have p6462_0 := h6462c.1
                                    have p6462_1 := h6462c.2.1
                                    have p6462_2 := h6462c.2.2.1
                                    have p6462_3 := h6462c.2.2.2
                                    linarith only [hlam, p6462_0]
                                · linarith only [h5744, h6359, h6419, h6420, h6424, h6428, h6461, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6362, h6419, hlam]
                  · linarith only [h0, h6361, h6418, hlam]
                · linarith only [h0, h6360, h6417, hlam]
              · linarith only [h5744, h6359, h6416, hlam]
        · linarith only [h0, h6359, h6362, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6496 | h6496
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6497 | h6497
          · linarith only [h0, h5743, h6361, h6497, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6499 | h6499
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6500 | h6500
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6501 | h6501
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6502 | h6502
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6503 | h6503
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6504 | h6504
                      · linarith only [h0, h5743, h6361, h6497, h6502, h6504, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6506 | h6506
                        · linarith only [h0, h5743, h6361, h6502, h6506, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h0, h5743, h6361, h6499, h6501, h6502, h6506, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h6361, h6502, h6503, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6510 | h6510
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6511 | h6511
                      · linarith only [h0, h5743, h6361, h6497, h6502, h6511, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6513 | h6513
                        · linarith only [h0, h5743, h6502, h6513, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h5743, h6499, h6501, h6502, h6513, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h0, h6359, h6361, h6496, h6510, hc04, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h6359, h6360, h6501, hc02, hc15, hlam, hphi, ht0b, ht5b]
              · linarith only [h0, h5743, h6361, h6499, h6500, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6519 | h6519
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6520 | h6520
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6521 | h6521
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6522 | h6522
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6523 | h6523
                      · linarith only [h0, h5743, h6361, h6521, h6523, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6525 | h6525
                        · linarith only [h0, h5743, h6361, h6499, h6521, h6525, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6527 | h6527
                          · linarith only [h0, h6359, h6361, h6520, h6521, h6523, h6525, h6527, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6529 | h6529
                            · linarith only [h5743, h6499, h6520, h6529, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6531 | h6531
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6532 | h6532
                                · rcases h0bigk with h6533c | h6533c | h6533c | h6533c | h6533c | h6533c | h6533c | h6533c | h6533c | h6533c | h6533c | h6533c | h6533c | h6533c | h6533c | h6533c | h6533c | h6533c | h6533c | h6533c | h6533c | h6533c | h6533c | h6533c | h6533c
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [hlam, p6533_0]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h0, hlam, p6533_1]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h0, h6361, h6521, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6533_1]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h5744, hlam, p6533_1]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h0, h6361, h6521, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6533_1]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h6361, h6521, hc01, hc12, hlam, hphi, p6533_1]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [hlam, p6533_0]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h5743, h6361, h6520, h6521, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6533_1]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h6361, hlam, p6533_1]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h6359, h6361, h6521, h6522, h6531, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p6533_1]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h5743, hlam, p6533_1]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h6360, hlam, p6533_1]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [hlam, p6533_0]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h6497, hlam, p6533_1]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h6499, hlam, p6533_1]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h5743, h6520, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6533_1]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h6361, h6521, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6533_1]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h5743, h6361, h6520, h6521, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6533_1]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [hlam, p6533_0]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h5743, h6361, h6499, h6520, h6521, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6533_1]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h6359, hlam, p6533_0]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h6496, hlam, p6533_1]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h0, h5743, h6359, h6520, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6533_1]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [h6519, hlam, p6533_1]
                                  · have p6533_0 := h6533c.1
                                    have p6533_1 := h6533c.2.1
                                    have p6533_2 := h6533c.2.2.1
                                    have p6533_3 := h6533c.2.2.2
                                    linarith only [hlam, p6533_0]
                                · linarith only [h0, h5743, h6361, h6520, h6521, h6523, h6532, hc23, hc45, hlam, hphi, ht34]
                              · linarith only [h0, h6359, h6361, h6519, h6520, h6525, h6531, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                    · linarith only [h0, h6361, h6521, h6522, hc01, hc25, hlam, hphi, ht12]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6562 | h6562
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6563 | h6563
                      · linarith only [h0, h5743, h6497, h6521, h6563, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6565 | h6565
                        · linarith only [h5743, h6499, h6565, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6567 | h6567
                          · linarith only [h0, h6359, h6520, h6521, h6563, h6565, h6567, hlam]
                          · linarith only [h0, h6359, h6520, h6521, h6565, h6567, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h6359, h6361, h6496, h6562, hc04, hc15, hlam, hphi, ht0b, ht5b]
                · linarith only [h0, h6360, h6520, hlam]
              · linarith only [h0, h6359, h6361, h6519, hlam]
        · linarith only [h0, h6359, h6496, hlam]
    · linarith only [h0, h5743, h6360, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h6575 | h6575
    · rcases m.htr 0 2 4 (by decide) (by decide) with h6576 | h6576
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6577 | h6577
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6578 | h6578
          · linarith only [h5743, h5744, h6578, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6580 | h6580
            · linarith only [h5743, h6359, h6580, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6582 | h6582
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6583 | h6583
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6584 | h6584
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6585 | h6585
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6586 | h6586
                      · linarith only [h5743, h5744, h6578, h6584, h6586, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6588 | h6588
                        · linarith only [h5743, h6359, h6580, h6588, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6590 | h6590
                          · linarith only [h5743, h5744, h6575, h6586, h6590, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6592 | h6592
                            · linarith only [h5743, h6359, h6583, h6588, h6592, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6594 | h6594
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6595 | h6595
                                · rcases h0bigk with h6596c | h6596c | h6596c | h6596c | h6596c | h6596c | h6596c | h6596c | h6596c | h6596c | h6596c | h6596c | h6596c | h6596c | h6596c | h6596c | h6596c | h6596c | h6596c | h6596c | h6596c | h6596c | h6596c | h6596c | h6596c
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [hlam, p6596_0]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [h0, hlam, p6596_1]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [h5744, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6596_1]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [h5744, hlam, p6596_1]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [h6359, hlam, p6596_1]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6596_1]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [hlam, p6596_0]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    rcases p6596_3 (m.d 0 1) (by simp) with h6604 | h6604
                                    · linarith only [h0, h6604, hlam]
                                    · linarith only [h5743, h6604, hlam]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [h0, h5743, h6359, h6582, h6583, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6596_1]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [h0, h5743, h6359, h6583, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6596_1]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [h5743, hlam, p6596_1]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [h6575, hlam, p6596_1]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [hlam, p6596_0]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [h6578, hlam, p6596_1]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [h6580, hlam, p6596_1]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [h5743, h6583, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6596_1]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [h6576, hlam, p6596_0]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [h5743, h6578, h6583, hc23, hc34, hlam, hphi, p6596_1]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [hlam, p6596_0]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [h5743, h6359, h6578, h6583, hc23, hc34, hlam, hphi, p6596_1]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [h5743, h6583, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6596_1]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [h6577, hlam, p6596_1]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [h5743, h6359, h6583, h6588, hc23, hc35, hlam, hphi, p6596_1]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [h6582, hlam, p6596_1]
                                  · have p6596_0 := h6596c.1
                                    have p6596_1 := h6596c.2.1
                                    have p6596_2 := h6596c.2.2.1
                                    have p6596_3 := h6596c.2.2.2
                                    linarith only [hlam, p6596_0]
                                · linarith only [h0, h5743, h5744, h6576, h6583, h6586, h6594, h6595, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6625 | h6625
                                · rcases h0bigk with h6626c | h6626c | h6626c | h6626c | h6626c | h6626c | h6626c | h6626c | h6626c | h6626c | h6626c | h6626c | h6626c | h6626c | h6626c | h6626c | h6626c | h6626c | h6626c | h6626c | h6626c | h6626c | h6626c | h6626c | h6626c
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [hlam, p6626_0]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [h0, hlam, p6626_1]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [h0, h5743, h6583, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6626_1]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [h5744, hlam, p6626_1]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [h6359, hlam, p6626_1]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [h0, hc01, hc12, hlam, hphi, p6626_1]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [hlam, p6626_0]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    rcases p6626_3 (m.d 0 1) (by simp) with h6634 | h6634
                                    · linarith only [h0, h6634, hlam]
                                    · linarith only [h5743, h6634, hlam]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [h0, h6582, h6590, h6594, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6626_1]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [h0, h5743, h6359, h6583, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6626_1]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [h5743, hlam, p6626_1]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [h6575, hlam, p6626_1]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [hlam, p6626_0]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [h6578, hlam, p6626_1]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [h6580, hlam, p6626_1]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [h5743, h6583, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6626_1]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [h6576, hlam, p6626_0]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [h5743, h6578, h6583, hc23, hc34, hlam, hphi, p6626_1]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [hlam, p6626_0]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [h5743, h6359, h6578, h6583, hc23, hc34, hlam, hphi, p6626_1]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [h5743, h6583, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6626_1]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [h6577, hlam, p6626_1]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [h5743, h6359, h6583, h6588, h6625, hc23, hc34, hlam, hphi, p6626_1]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [h6582, hlam, p6626_1]
                                  · have p6626_0 := h6626c.1
                                    have p6626_1 := h6626c.2.1
                                    have p6626_2 := h6626c.2.2.1
                                    have p6626_3 := h6626c.2.2.2
                                    linarith only [hlam, p6626_0]
                                · linarith only [h5743, h5744, h6583, h6586, h6625, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6576, h6577, h6582, h6585, hlam]
                  · linarith only [h0, h6576, h6584, hlam]
                · linarith only [h0, h6575, h6583, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6658 | h6658
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6659 | h6659
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6660 | h6660
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6661 | h6661
                      · linarith only [h5743, h5744, h6578, h6661, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6663 | h6663
                        · linarith only [h5743, h6580, h6663, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6665 | h6665
                          · linarith only [h5743, h5744, h6658, h6661, h6665, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6667 | h6667
                            · linarith only [h5743, h6359, h6575, h6663, h6667, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6669 | h6669
                              · linarith only [h0, h5743, h5744, h6576, h6582, h6658, h6669, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6671 | h6671
                                · linarith only [h5743, h5744, h6582, h6658, h6671, hc23, hc34, hlam, hphi]
                                · linarith only [h5743, h5744, h6658, h6661, h6671, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h6577, h6660, hlam]
                  · linarith only [h0, h6576, h6659, hlam]
                · linarith only [h0, h6575, h6658, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6677 | h6677
          · linarith only [h5743, h5744, h6677, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6679 | h6679
            · linarith only [h0, h5743, h6577, h6679, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6681 | h6681
              · linarith only [h6576, h6577, h6681, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6683 | h6683
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6684 | h6684
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6685 | h6685
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6686 | h6686
                      · linarith only [h5743, h5744, h6576, h6577, h6677, h6685, h6686, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6688 | h6688
                        · linarith only [h5743, h5744, h6576, h6577, h6679, h6688, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6690 | h6690
                          · linarith only [h5743, h5744, h6683, h6686, h6690, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6692 | h6692
                            · linarith only [h5743, h5744, h6576, h6577, h6683, h6685, h6688, h6692, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6694 | h6694
                              · linarith only [h5743, h5744, h6576, h6577, h6681, h6683, h6685, h6694, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6696 | h6696
                                · linarith only [h0, h5743, h6577, h6683, h6694, h6696, hc23, hc34, hlam, hphi]
                                · linarith only [h5743, h5744, h6683, h6686, h6696, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6699 | h6699
                      · linarith only [h5743, h6677, h6699, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6701 | h6701
                        · linarith only [h5743, h6679, h6701, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6703 | h6703
                          · linarith only [h5743, h5744, h6683, h6699, h6703, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6705 | h6705
                            · linarith only [h5743, h5744, h6683, h6685, h6699, h6701, h6705, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h5743, h5744, h6683, h6684, h6685, h6705, hc23, hc35, hlam, hphi]
                  · linarith only [h0, h5743, h6576, h6683, h6684, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h6575, h6683, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h6710 | h6710
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6711 | h6711
          · linarith only [h0, h5743, h6576, h6711, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6713 | h6713
            · linarith only [h5743, h6359, h6713, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6715 | h6715
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6716 | h6716
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6717 | h6717
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6718 | h6718
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6719 | h6719
                      · linarith only [h5743, h6359, h6576, h6710, h6711, h6717, h6719, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6721 | h6721
                        · linarith only [h5743, h6359, h6713, h6721, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6723 | h6723
                          · linarith only [h6575, h6576, h6717, h6719, h6723, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6725 | h6725
                            · linarith only [h5743, h6359, h6576, h6710, h6716, h6717, h6721, h6725, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6727 | h6727
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6728 | h6728
                                · rcases h0bigk with h6729c | h6729c | h6729c | h6729c | h6729c | h6729c | h6729c | h6729c | h6729c | h6729c | h6729c | h6729c | h6729c | h6729c | h6729c | h6729c | h6729c | h6729c | h6729c | h6729c | h6729c | h6729c | h6729c | h6729c | h6729c
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [hlam, p6729_0]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h0, hlam, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h6359, h6576, h6710, h6717, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h5744, hlam, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h6359, hlam, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h6576, h6717, hc01, hc12, hlam, hphi, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [hlam, p6729_0]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h5743, h6576, h6716, h6717, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h6576, hlam, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h6576, h6717, hc05, hc12, hlam, hphi, ht01, ht0b, ht5b, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h5743, hlam, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h6575, hlam, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [hlam, p6729_0]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h6711, hlam, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h6713, hlam, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h5743, h6716, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h6576, h6717, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h5743, h6576, h6716, h6717, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [hlam, p6729_0]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h5743, h6359, h6576, h6716, h6717, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h5743, h6710, h6716, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h6710, hlam, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h5743, h6576, h6710, h6716, h6717, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [h6715, hlam, p6729_1]
                                  · have p6729_0 := h6729c.1
                                    have p6729_1 := h6729c.2.1
                                    have p6729_2 := h6729c.2.2.1
                                    have p6729_3 := h6729c.2.2.2
                                    linarith only [hlam, p6729_0]
                                · linarith only [h0, h5743, h6576, h6716, h6717, h6719, h6728, hc23, hc45, hlam, hphi, ht34]
                              · linarith only [h6576, h6710, h6715, h6727, hlam]
                    · linarith only [h6576, h6710, h6718, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6758 | h6758
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6759 | h6759
                      · linarith only [h5743, h6359, h6711, h6717, h6758, h6759, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6761 | h6761
                        · linarith only [h5743, h6359, h6717, h6758, h6761, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6763 | h6763
                          · linarith only [h5743, h5744, h6359, h6576, h6716, h6717, h6758, h6759, h6763, hc02, hc24, hlam, hphi]
                          · linarith only [h5743, h6359, h6716, h6717, h6758, h6763, hc23, hc34, hlam, hphi]
                    · linarith only [h0, h5743, h6576, h6710, h6716, h6758, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h0, h6575, h6716, hlam]
              · linarith only [h6576, h6710, h6715, hlam]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h6769 | h6769
          · linarith only [h0, h5743, h6576, h6769, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6771 | h6771
            · linarith only [h5743, h6359, h6771, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6773 | h6773
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6774 | h6774
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6775 | h6775
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6776 | h6776
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6777 | h6777
                      · linarith only [h0, h5743, h6710, h6769, h6776, h6777, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6779 | h6779
                        · linarith only [h0, h5743, h6710, h6771, h6779, hlam]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6781 | h6781
                          · linarith only [h5744, h6575, h6576, h6775, h6777, h6781, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6783 | h6783
                            · linarith only [h0, h5743, h6576, h6774, h6775, h6779, h6783, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6785 | h6785
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h6786 | h6786
                                · rcases h0bigk with h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [hlam, p6787_0]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h0, hlam, p6787_1]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h0, h6710, h6775, h6785, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6787_1]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h5744, hlam, p6787_1]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h6359, hlam, p6787_1]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h6710, h6775, h6785, hc01, hc12, hlam, hphi, p6787_1]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [hlam, p6787_0]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h5743, h6710, h6774, h6775, h6785, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6787_1]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h6576, hlam, p6787_1]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h6710, hlam, p6787_0]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h5743, hlam, p6787_1]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h6575, hlam, p6787_1]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [hlam, p6787_0]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h6769, hlam, p6787_1]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h6771, hlam, p6787_1]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h5743, h6774, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6787_1]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h6576, h6775, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p6787_1]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h5743, h6576, h6774, h6775, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6787_1]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [hlam, p6787_0]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h0, h5743, h6576, h6710, h6774, h6775, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6787_1]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h5743, h6774, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p6787_1]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h0, h5743, h6710, h6774, h6775, h6785, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6787_1]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h5743, h6710, h6774, h6775, h6785, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p6787_1]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [h6773, hlam, p6787_1]
                                  · have p6787_0 := h6787c.1
                                    have p6787_1 := h6787c.2.1
                                    have p6787_2 := h6787c.2.2.1
                                    have p6787_3 := h6787c.2.2.2
                                    linarith only [hlam, p6787_0]
                                · linarith only [h6576, h6773, h6775, h6777, h6786, hlam]
                              · linarith only [h6576, h6773, h6785, hlam]
                    · linarith only [h0, h5743, h6576, h6774, h6775, h6776, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6816 | h6816
                    · linarith only [h0, h5743, h6710, h6774, h6775, h6816, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6818 | h6818
                      · linarith only [h0, h5743, h6775, h6818, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6820 | h6820
                        · linarith only [h0, h5743, h6775, h6820, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6822 | h6822
                          · linarith only [h0, h5743, h6774, h6775, h6818, h6822, hlam]
                          · linarith only [h0, h5743, h6774, h6775, h6822, hc23, hc34, hlam, hphi]
                · linarith only [h0, h5743, h6575, h6774, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h6826 | h6826
                · rcases m.htr 1 2 4 (by decide) (by decide) with h6827 | h6827
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6828 | h6828
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6829 | h6829
                      · linarith only [h0, h5743, h6576, h6773, h6829, hc34, hc45, hlam, hphi]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6831 | h6831
                        · linarith only [h0, h5743, h6576, h6827, h6831, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6833 | h6833
                          · linarith only [h6575, h6576, h6827, h6829, h6833, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h6835 | h6835
                            · linarith only [h5743, h6359, h6826, h6831, h6835, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h6837 | h6837
                              · linarith only [h0, h6576, h6773, h6827, h6837, hc01, hc12, hlam, hphi]
                              · linarith only [h0, h5743, h6576, h6826, h6837, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h5743, h6576, h6826, h6827, h6828, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h6841 | h6841
                    · linarith only [h0, h5743, h6710, h6826, h6827, h6841, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h6843 | h6843
                      · linarith only [h0, h5743, h6827, h6843, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h6845 | h6845
                        · linarith only [h0, h5743, h6827, h6845, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h6847 | h6847
                          · linarith only [h0, h5743, h6826, h6827, h6843, h6847, hlam]
                          · linarith only [h0, h5743, h6826, h6827, h6847, hc23, hc34, hlam, hphi]
                · linarith only [h0, h5743, h6575, h6826, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · linarith only [h0, h5743, h6575, hlam]

set_option maxHeartbeats 9598000 in
set_option maxHeartbeats 9598000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s7_x0 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5743 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0 := hg0
  rcases m.htr 0 1 4 (by decide) (by decide) with h5744 | h5744
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s7_x0_x0 m hb0 hb2 hb3 hb5 hg0 h5743 h5744
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s7_x0_x1 m hb0 hb2 hb3 hb5 hg0 h5743 h5744

set_option maxHeartbeats 9598000 in
set_option maxHeartbeats 9598000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s7_x1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h5743 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  have h0 := hg0
  exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s8 m hb0 hb2 hb3 hb5 h0 h5743

set_option maxHeartbeats 9598000 in
set_option maxHeartbeats 9598000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s7 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
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
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h5743 | h5743
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s7_x0 m hb0 hb2 hb3 hb5 hg0 h5743
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s7_x1 m hb0 hb2 hb3 hb5 hg0 h5743

set_option maxHeartbeats 21084000 in
set_option maxHeartbeats 21084000 in
theorem r1l7_20_12_13_15_H_I_L_I_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s0 m hb0 hb2 hb3 hb5 h0
  · exact r1l7_20_12_13_15_H_I_L_I_L_I_L_I_s7 m hb0 hb2 hb3 hb5 h0

end R2N4
