import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 7594000 in
set_option maxHeartbeats 7594000 in
theorem r1l7_11_23_L_I_H_I_s9_x0_x0_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (hg3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (hg4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h6364 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
    (h6365 : (m.d 0 3 + m.lam ≤ m.d 3 4 ∧ m.d 0 3 < m.d 0 4 ∧ m.d 0 4 < m.d 3 4))
    (h6366 : (m.d 0 3 + m.lam ≤ m.d 3 5 ∧ m.d 0 3 < m.d 0 5 ∧ m.d 0 5 < m.d 3 5))
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
  rcases m.htr 0 4 5 (by decide) (by decide) with h6367 | h6367
  · rcases m.htr 1 2 3 (by decide) (by decide) with h6368 | h6368
    · linarith only [h0, h4, h6364, h6368, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h6370 | h6370
      · rcases m.htr 1 2 5 (by decide) (by decide) with h6371 | h6371
        · rcases m.htr 1 3 4 (by decide) (by decide) with h6372 | h6372
          · rcases m.htr 1 3 5 (by decide) (by decide) with h6373 | h6373
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6374 | h6374
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6375 | h6375
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6376 | h6376
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6377 | h6377
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6378 | h6378
                      · rcases h1bigk with h6379c | h6379c | h6379c | h6379c | h6379c | h6379c | h6379c | h6379c | h6379c | h6379c | h6379c | h6379c | h6379c | h6379c | h6379c | h6379c | h6379c | h6379c | h6379c | h6379c | h6379c | h6379c | h6379c | h6379c | h6379c
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [hlam, p6379_0]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [h6370, h6375, h6378, hc01, hc45, hlam, hphi, ht0b, ht5b, p6379_1]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [h6368, h6370, h6375, h6378, hc01, hc45, hlam, hphi, ht0b, ht5b, p6379_1]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          rcases p6379_3 (m.d 0 1) (by simp) with h6383 | h6383
                          · rcases p6379_3 (m.d 1 2) (by simp) with h6384 | h6384
                            · linarith only [h0, h6384, hlam]
                            · linarith only [h6370, h6384, hlam]
                          · linarith only [h6383, hlam, p6379_0]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          rcases p6379_3 (m.d 0 1) (by simp) with h6388 | h6388
                          · rcases p6379_3 (m.d 1 2) (by simp) with h6389 | h6389
                            · linarith only [h0, h6389, hlam]
                            · linarith only [h6371, h6389, hlam]
                          · linarith only [h6388, hlam, p6379_0]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [h0, hlam, p6379_0]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [hlam, p6379_0]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [h6368, hlam, p6379_0]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [h0, h4, h6370, h6375, h6378, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6379_1]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          rcases p6379_3 (m.d 0 1) (by simp) with h6397 | h6397
                          · rcases p6379_3 (m.d 1 2) (by simp) with h6398 | h6398
                            · rcases p6379_3 (m.d 1 3) (by simp) with h6399 | h6399
                              · rcases p6379_3 (m.d 1 4) (by simp) with h6400 | h6400
                                · linarith only [h6370, h6400, hlam]
                                · linarith only [h6374, h6400, hlam]
                              · linarith only [h6373, h6399, hlam]
                            · linarith only [h6371, h6398, hlam]
                          · linarith only [h3, h6397, hlam]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [h1, hlam, p6379_0]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [h1, h6370, h6375, h6378, hc01, hc45, hlam, hphi, ht0b, ht5b, p6379_1]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [hlam, p6379_0]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [h1, h6370, h6375, h6378, hc01, hc45, hlam, hphi, ht0b, ht5b, p6379_1]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          rcases p6379_3 (m.d 0 1) (by simp) with h6410 | h6410
                          · rcases p6379_3 (m.d 1 2) (by simp) with h6411 | h6411
                            · linarith only [h6368, h6411, hlam]
                            · linarith only [h6371, h6411, hlam]
                          · linarith only [h3, h6410, hlam]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [h2, hlam, p6379_0]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [h6370, hlam, p6379_1]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [h6372, hlam, p6379_0]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [hlam, p6379_0]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          rcases p6379_3 (m.d 0 1) (by simp) with h6419 | h6419
                          · rcases p6379_3 (m.d 1 2) (by simp) with h6420 | h6420
                            · rcases p6379_3 (m.d 1 3) (by simp) with h6421 | h6421
                              · rcases p6379_3 (m.d 1 4) (by simp) with h6422 | h6422
                                · rcases p6379_3 (m.d 1 5) (by simp) with h6423 | h6423
                                  · linarith only [h6374, h6423, hlam]
                                  · rcases h3bigk with h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c | h6425c
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [hlam, p6425_0]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [h4, h6368, h6370, h6371, h6376, h6378, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6379_1, p6425_1]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [h4, hlam, p6425_1]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [h4, h6378, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6425_1]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      rcases p6425_3 (m.d 0 3) (by simp) with h6430 | h6430
                                      · rcases p6425_3 (m.d 1 3) (by simp) with h6431 | h6431
                                        · linarith only [h1, h6431, hlam]
                                        · linarith only [h6373, h6431, hlam]
                                      · linarith only [h6430, hlam, p6425_0]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [h1, hlam, p6425_0]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [hlam, p6425_0]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [h6368, hlam, p6425_1]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [h6378, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p6425_1]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [h1, h6378, hc01, hc45, hlam, hphi, ht0b, ht5b, p6425_1]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [h4, hc02, hc23, hlam, hphi, p6425_1]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [h6368, h6370, h6371, h6376, h6378, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6379_1, p6425_1]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [hlam, p6425_0]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [h6378, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6425_1]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      rcases p6425_3 (m.d 0 3) (by simp) with h6444 | h6444
                                      · linarith only [h4, h6444, hlam]
                                      · linarith only [h6366, h6444, hlam]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [h6365, hlam, p6425_0]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [h6372, hlam, p6425_0]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [h6375, hlam, p6425_0]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [hlam, p6425_0]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [h6364, h6375, h6378, hc02, hc45, hlam, hphi, ht0b, ht5b, p6425_1]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [h6366, hlam, p6425_0]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [h6373, hlam, p6425_0]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [h6376, hlam, p6425_0]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [h6378, hlam, p6425_0]
                                    · have p6425_0 := h6425c.1
                                      have p6425_1 := h6425c.2.1
                                      have p6425_2 := h6425c.2.2.1
                                      have p6425_3 := h6425c.2.2.2
                                      linarith only [hlam, p6425_0]
                                · linarith only [h6374, h6422, hlam]
                              · linarith only [h6373, h6421, hlam]
                            · linarith only [h6371, h6420, hlam]
                          · linarith only [h3, h6419, hlam]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [h3, hlam, p6379_0]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [h6371, hlam, p6379_1]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [h6373, hlam, p6379_0]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [h6374, hlam, p6379_0]
                        · have p6379_0 := h6379c.1
                          have p6379_1 := h6379c.2.1
                          have p6379_2 := h6379c.2.2.1
                          have p6379_3 := h6379c.2.2.2
                          linarith only [hlam, p6379_0]
                      · linarith only [h0, h4, h6370, h6377, h6378, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6467 | h6467
                      · linarith only [h6375, h6377, h6467, hlam]
                      · rcases h1bigk with h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c | h6469c
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [hlam, p6469_0]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [h6370, h6374, h6375, h6377, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6469_1]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [h6368, h6370, h6374, h6375, h6377, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6469_1]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [h6374, h6375, h6377, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6469_1]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          rcases p6469_3 (m.d 0 1) (by simp) with h6474 | h6474
                          · rcases p6469_3 (m.d 1 2) (by simp) with h6475 | h6475
                            · linarith only [h0, h6475, hlam]
                            · linarith only [h6371, h6475, hlam]
                          · linarith only [h6474, hlam, p6469_0]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [h0, hlam, p6469_0]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [hlam, p6469_0]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [h6368, hlam, p6469_0]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [h6374, h6375, h6377, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p6469_1]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [h0, h4, h6374, h6375, h6377, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6469_1]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [h1, hlam, p6469_0]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [h1, h6370, h6375, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6469_1]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [hlam, p6469_0]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [h1, h6374, h6375, h6377, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6469_1]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [h1, h6374, h6375, h6377, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6469_1]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [h2, hlam, p6469_0]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [h6370, hlam, p6469_1]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [h6372, hlam, p6469_0]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [hlam, p6469_0]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [h0, h6370, h6374, h6375, h6377, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6469_1]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [h3, hlam, p6469_0]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [h6371, hlam, p6469_1]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [h6373, hlam, p6469_0]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [h6374, hlam, p6469_0]
                        · have p6469_0 := h6469c.1
                          have p6469_1 := h6469c.2.1
                          have p6469_2 := h6469c.2.2.1
                          have p6469_3 := h6469c.2.2.2
                          linarith only [hlam, p6469_0]
                  · linarith only [h4, h6366, h6376, hlam]
                · linarith only [h4, h6365, h6375, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6501 | h6501
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6502 | h6502
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6503 | h6503
                    · linarith only [h6370, h6374, h6503, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6505 | h6505
                      · linarith only [h6370, h6374, h6501, h6505, hlam]
                      · rcases h1bigk with h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c | h6507c
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          linarith only [hlam, p6507_0]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          rcases p6507_3 (m.d 0 1) (by simp) with h6509 | h6509
                          · rcases p6507_3 (m.d 1 2) (by simp) with h6510 | h6510
                            · linarith only [h6510, hlam, p6507_0]
                            · rcases p6507_3 (m.d 1 3) (by simp) with h6512 | h6512
                              · linarith only [h1, h6512, hlam]
                              · linarith only [h6368, h6512, hlam]
                          · linarith only [h6509, hlam, p6507_0]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          rcases p6507_3 (m.d 0 1) (by simp) with h6516 | h6516
                          · rcases p6507_3 (m.d 1 2) (by simp) with h6517 | h6517
                            · linarith only [h0, h6517, hlam]
                            · rcases p6507_3 (m.d 1 3) (by simp) with h6519 | h6519
                              · linarith only [h6519, hlam, p6507_0]
                              · rcases p6507_3 (m.d 1 4) (by simp) with h6521 | h6521
                                · linarith only [h2, h6521, hlam]
                                · rcases p6507_3 (m.d 1 5) (by simp) with h6523 | h6523
                                  · linarith only [h3, h6523, hlam]
                                  · rcases h3bigk with h6525c | h6525c | h6525c | h6525c | h6525c | h6525c | h6525c | h6525c | h6525c | h6525c | h6525c | h6525c | h6525c | h6525c | h6525c | h6525c | h6525c | h6525c | h6525c | h6525c | h6525c | h6525c | h6525c | h6525c | h6525c
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [hlam, p6525_0]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [h4, h6368, hc12, hc23, hlam, hphi, p6525_1]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [h4, hlam, p6525_1]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      rcases p6525_3 (m.d 0 3) (by simp) with h6529 | h6529
                                      · rcases p6525_3 (m.d 1 3) (by simp) with h6530 | h6530
                                        · linarith only [h1, h6530, hlam]
                                        · linarith only [h6372, h6530, hlam]
                                      · linarith only [h6529, hlam, p6525_0]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      rcases p6525_3 (m.d 0 3) (by simp) with h6534 | h6534
                                      · rcases p6525_3 (m.d 1 3) (by simp) with h6535 | h6535
                                        · linarith only [h1, h6535, hlam]
                                        · linarith only [h6373, h6535, hlam]
                                      · linarith only [h6534, hlam, p6525_0]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [h1, hlam, p6525_0]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [hlam, p6525_0]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [h6368, hlam, p6525_1]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6507_1, p6525_1]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [h6505, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6507_1, p6525_1]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [h4, h6364, h6367, h6370, h6374, h6501, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6525_1]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [h6368, h6371, h6501, h6503, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6525_1]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [hlam, p6525_0]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      rcases p6525_3 (m.d 0 3) (by simp) with h6547 | h6547
                                      · linarith only [h4, h6547, hlam]
                                      · linarith only [h6365, h6547, hlam]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      rcases p6525_3 (m.d 0 3) (by simp) with h6550 | h6550
                                      · linarith only [h4, h6550, hlam]
                                      · linarith only [h6366, h6550, hlam]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [h6365, hlam, p6525_0]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [h6372, hlam, p6525_0]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [h6501, hlam, p6525_0]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [hlam, p6525_0]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [h6505, hlam, p6525_1]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [h6366, hlam, p6525_0]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [h6373, hlam, p6525_0]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [h6502, hlam, p6525_0]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [h6366, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p6525_1]
                                    · have p6525_0 := h6525c.1
                                      have p6525_1 := h6525c.2.1
                                      have p6525_2 := h6525c.2.2.1
                                      have p6525_3 := h6525c.2.2.2
                                      linarith only [hlam, p6525_0]
                          · linarith only [h6516, hlam, p6507_0]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          rcases p6507_3 (m.d 0 1) (by simp) with h6564 | h6564
                          · rcases p6507_3 (m.d 1 2) (by simp) with h6565 | h6565
                            · linarith only [h0, h6565, hlam]
                            · linarith only [h6370, h6565, hlam]
                          · linarith only [h6564, hlam, p6507_0]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          rcases p6507_3 (m.d 0 1) (by simp) with h6569 | h6569
                          · rcases p6507_3 (m.d 1 2) (by simp) with h6570 | h6570
                            · linarith only [h0, h6570, hlam]
                            · linarith only [h6371, h6570, hlam]
                          · linarith only [h6569, hlam, p6507_0]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          linarith only [h0, hlam, p6507_0]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          linarith only [hlam, p6507_0]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          linarith only [h6368, hlam, p6507_0]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          rcases p6507_3 (m.d 0 1) (by simp) with h6577 | h6577
                          · rcases p6507_3 (m.d 1 2) (by simp) with h6578 | h6578
                            · rcases p6507_3 (m.d 1 3) (by simp) with h6579 | h6579
                              · rcases p6507_3 (m.d 1 4) (by simp) with h6580 | h6580
                                · linarith only [h6370, h6580, hlam]
                                · rcases p6507_3 (m.d 1 5) (by simp) with h6582 | h6582
                                  · linarith only [h6371, h6582, hlam]
                                  · linarith only [h6374, h6582, hlam]
                              · linarith only [h6372, h6579, hlam]
                            · linarith only [h6370, h6578, hlam]
                          · linarith only [h2, h6577, hlam]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          rcases p6507_3 (m.d 0 1) (by simp) with h6588 | h6588
                          · rcases p6507_3 (m.d 1 2) (by simp) with h6589 | h6589
                            · rcases p6507_3 (m.d 1 3) (by simp) with h6590 | h6590
                              · rcases p6507_3 (m.d 1 4) (by simp) with h6591 | h6591
                                · linarith only [h6370, h6591, hlam]
                                · rcases p6507_3 (m.d 1 5) (by simp) with h6593 | h6593
                                  · linarith only [h6371, h6593, hlam]
                                  · rcases h3bigk with h6595c | h6595c | h6595c | h6595c | h6595c | h6595c | h6595c | h6595c | h6595c | h6595c | h6595c | h6595c | h6595c | h6595c | h6595c | h6595c | h6595c | h6595c | h6595c | h6595c | h6595c | h6595c | h6595c | h6595c | h6595c
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [hlam, p6595_0]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [h1, h6368, h6370, h6374, h6501, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6507_1, p6595_1]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [h4, hlam, p6595_1]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      rcases p6595_3 (m.d 0 3) (by simp) with h6599 | h6599
                                      · rcases p6595_3 (m.d 1 3) (by simp) with h6600 | h6600
                                        · linarith only [h1, h6600, hlam]
                                        · linarith only [h6372, h6600, hlam]
                                      · linarith only [h6599, hlam, p6595_0]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      rcases p6595_3 (m.d 0 3) (by simp) with h6604 | h6604
                                      · rcases p6595_3 (m.d 1 3) (by simp) with h6605 | h6605
                                        · linarith only [h1, h6605, hlam]
                                        · linarith only [h6373, h6605, hlam]
                                      · linarith only [h6604, hlam, p6595_0]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [h1, hlam, p6595_0]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [hlam, p6595_0]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [h6368, hlam, p6595_1]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6595_1]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p6595_1]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [h0, h4, h6370, h6374, h6501, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6507_1, p6595_1]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [h6368, h6370, h6374, h6501, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6507_1, p6595_1]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [hlam, p6595_0]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      rcases p6595_3 (m.d 0 3) (by simp) with h6617 | h6617
                                      · linarith only [h4, h6617, hlam]
                                      · linarith only [h6365, h6617, hlam]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      rcases p6595_3 (m.d 0 3) (by simp) with h6620 | h6620
                                      · linarith only [h4, h6620, hlam]
                                      · linarith only [h6366, h6620, hlam]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [h6365, hlam, p6595_0]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [h6372, hlam, p6595_0]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [h6501, hlam, p6595_0]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [hlam, p6595_0]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [h6505, hlam, p6595_1]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [h6366, hlam, p6595_0]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [h6373, hlam, p6595_0]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [h6502, hlam, p6595_0]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [h6366, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p6595_1]
                                    · have p6595_0 := h6595c.1
                                      have p6595_1 := h6595c.2.1
                                      have p6595_2 := h6595c.2.2.1
                                      have p6595_3 := h6595c.2.2.2
                                      linarith only [hlam, p6595_0]
                              · linarith only [h6373, h6590, hlam]
                            · linarith only [h6371, h6589, hlam]
                          · linarith only [h3, h6588, hlam]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          linarith only [h1, hlam, p6507_0]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          linarith only [h1, h6370, h6501, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6507_1]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          linarith only [hlam, p6507_0]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          rcases p6507_3 (m.d 0 1) (by simp) with h6639 | h6639
                          · rcases p6507_3 (m.d 1 2) (by simp) with h6640 | h6640
                            · linarith only [h6368, h6640, hlam]
                            · linarith only [h6370, h6640, hlam]
                          · linarith only [h2, h6639, hlam]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          rcases p6507_3 (m.d 0 1) (by simp) with h6644 | h6644
                          · rcases p6507_3 (m.d 1 2) (by simp) with h6645 | h6645
                            · linarith only [h6368, h6645, hlam]
                            · linarith only [h6371, h6645, hlam]
                          · linarith only [h3, h6644, hlam]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          linarith only [h2, hlam, p6507_0]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          linarith only [h6370, hlam, p6507_1]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          linarith only [h6372, hlam, p6507_0]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          linarith only [hlam, p6507_0]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          linarith only [h6374, hlam, p6507_1]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          linarith only [h3, hlam, p6507_0]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          linarith only [h6371, hlam, p6507_1]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          linarith only [h6373, hlam, p6507_0]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          linarith only [h4, h6364, h6367, h6370, h6374, h6501, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6507_1]
                        · have p6507_0 := h6507c.1
                          have p6507_1 := h6507c.2.1
                          have p6507_2 := h6507c.2.2.1
                          have p6507_3 := h6507c.2.2.2
                          linarith only [hlam, p6507_0]
                  · linarith only [h4, h6366, h6502, hlam]
                · linarith only [h4, h6365, h6501, hlam]
            · linarith only [h6368, h6371, h6373, hlam]
          · linarith only [h6368, h6370, h6372, hlam]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h6663 | h6663
          · rcases m.htr 1 3 5 (by decide) (by decide) with h6664 | h6664
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6665 | h6665
              · linarith only [h6370, h6371, h6665, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6667 | h6667
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6668 | h6668
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6669 | h6669
                    · linarith only [h6370, h6371, h6665, h6669, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · linarith only [h4, h6364, h6367, h6371, h6669, hc12, hc23, hlam, hphi]
                  · linarith only [h4, h6364, h6367, h6664, h6665, h6668, hlam]
                · linarith only [h4, h6364, h6367, h6665, h6667, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6674 | h6674
              · linarith only [h6368, h6370, h6664, h6674, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6676 | h6676
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6677 | h6677
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6678 | h6678
                    · linarith only [h6364, h6366, h6367, h6368, h6370, h6664, h6674, h6678, hc02, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h4, h6364, h6367, h6368, h6664, h6677, h6678, hc12, hc23, hlam, hphi]
                  · linarith only [h4, h6366, h6677, hlam]
                · linarith only [h4, h6364, h6366, h6367, h6368, h6370, h6664, h6676, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
          · linarith only [h6368, h6370, h6663, hlam]
      · linarith only [h4, h6364, h6370, hc12, hc23, hlam, hphi]
  · rcases m.htr 1 2 3 (by decide) (by decide) with h6685 | h6685
    · linarith only [h0, h4, h6364, h6685, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
    · rcases m.htr 1 2 4 (by decide) (by decide) with h6687 | h6687
      · rcases m.htr 1 2 5 (by decide) (by decide) with h6688 | h6688
        · rcases m.htr 1 3 4 (by decide) (by decide) with h6689 | h6689
          · rcases m.htr 1 3 5 (by decide) (by decide) with h6690 | h6690
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6691 | h6691
              · linarith only [h2, h6367, h6691, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6693 | h6693
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6694 | h6694
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6695 | h6695
                    · linarith only [h2, h6367, h6687, h6695, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6697 | h6697
                      · linarith only [h2, h6367, h6687, h6693, h6697, hlam]
                      · rcases h1bigk with h6699c | h6699c | h6699c | h6699c | h6699c | h6699c | h6699c | h6699c | h6699c | h6699c | h6699c | h6699c | h6699c | h6699c | h6699c | h6699c | h6699c | h6699c | h6699c | h6699c | h6699c | h6699c | h6699c | h6699c | h6699c
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          linarith only [hlam, p6699_0]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          rcases p6699_3 (m.d 0 1) (by simp) with h6701 | h6701
                          · rcases p6699_3 (m.d 1 2) (by simp) with h6702 | h6702
                            · linarith only [h6702, hlam, p6699_0]
                            · rcases p6699_3 (m.d 1 3) (by simp) with h6704 | h6704
                              · linarith only [h1, h6704, hlam]
                              · linarith only [h6685, h6704, hlam]
                          · linarith only [h6701, hlam, p6699_0]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          rcases p6699_3 (m.d 0 1) (by simp) with h6708 | h6708
                          · rcases p6699_3 (m.d 1 2) (by simp) with h6709 | h6709
                            · linarith only [h0, h6709, hlam]
                            · rcases p6699_3 (m.d 1 3) (by simp) with h6711 | h6711
                              · linarith only [h6711, hlam, p6699_0]
                              · rcases p6699_3 (m.d 1 4) (by simp) with h6713 | h6713
                                · linarith only [h2, h6713, hlam]
                                · rcases p6699_3 (m.d 1 5) (by simp) with h6715 | h6715
                                  · linarith only [h3, h6715, hlam]
                                  · rcases h3bigk with h6717c | h6717c | h6717c | h6717c | h6717c | h6717c | h6717c | h6717c | h6717c | h6717c | h6717c | h6717c | h6717c | h6717c | h6717c | h6717c | h6717c | h6717c | h6717c | h6717c | h6717c | h6717c | h6717c | h6717c | h6717c
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [hlam, p6717_0]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [h6685, h6688, h6695, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b, p6717_1]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [h4, hlam, p6717_1]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      rcases p6717_3 (m.d 0 3) (by simp) with h6721 | h6721
                                      · rcases p6717_3 (m.d 1 3) (by simp) with h6722 | h6722
                                        · linarith only [h1, h6722, hlam]
                                        · linarith only [h6689, h6722, hlam]
                                      · linarith only [h6721, hlam, p6717_0]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      rcases p6717_3 (m.d 0 3) (by simp) with h6726 | h6726
                                      · rcases p6717_3 (m.d 1 3) (by simp) with h6727 | h6727
                                        · linarith only [h1, h6727, hlam]
                                        · linarith only [h6690, h6727, hlam]
                                      · linarith only [h6726, hlam, p6717_0]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [h1, hlam, p6717_0]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [hlam, p6717_0]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [h6685, hlam, p6717_1]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6699_1, p6717_1]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [h6697, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6699_1, p6717_1]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [h0, h4, h6688, h6693, h6695, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6717_1]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [h6685, h6688, h6693, h6695, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6717_1]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [hlam, p6717_0]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      rcases p6717_3 (m.d 0 3) (by simp) with h6739 | h6739
                                      · linarith only [h4, h6739, hlam]
                                      · linarith only [h6365, h6739, hlam]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      rcases p6717_3 (m.d 0 3) (by simp) with h6742 | h6742
                                      · linarith only [h4, h6742, hlam]
                                      · linarith only [h6366, h6742, hlam]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [h6365, hlam, p6717_0]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [h6689, hlam, p6717_0]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [h6693, hlam, p6717_0]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [hlam, p6717_0]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [h6697, hlam, p6717_1]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [h6366, hlam, p6717_0]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [h6690, hlam, p6717_0]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [h6694, hlam, p6717_0]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [h6366, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p6717_1]
                                    · have p6717_0 := h6717c.1
                                      have p6717_1 := h6717c.2.1
                                      have p6717_2 := h6717c.2.2.1
                                      have p6717_3 := h6717c.2.2.2
                                      linarith only [hlam, p6717_0]
                          · linarith only [h6708, hlam, p6699_0]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          rcases p6699_3 (m.d 0 1) (by simp) with h6756 | h6756
                          · rcases p6699_3 (m.d 1 2) (by simp) with h6757 | h6757
                            · linarith only [h0, h6757, hlam]
                            · linarith only [h6687, h6757, hlam]
                          · linarith only [h6756, hlam, p6699_0]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          rcases p6699_3 (m.d 0 1) (by simp) with h6761 | h6761
                          · rcases p6699_3 (m.d 1 2) (by simp) with h6762 | h6762
                            · linarith only [h0, h6762, hlam]
                            · linarith only [h6688, h6762, hlam]
                          · linarith only [h6761, hlam, p6699_0]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          linarith only [h0, hlam, p6699_0]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          linarith only [hlam, p6699_0]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          linarith only [h6685, hlam, p6699_0]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          rcases p6699_3 (m.d 0 1) (by simp) with h6769 | h6769
                          · rcases p6699_3 (m.d 1 2) (by simp) with h6770 | h6770
                            · rcases p6699_3 (m.d 1 3) (by simp) with h6771 | h6771
                              · rcases p6699_3 (m.d 1 4) (by simp) with h6772 | h6772
                                · linarith only [h6687, h6772, hlam]
                                · rcases p6699_3 (m.d 1 5) (by simp) with h6774 | h6774
                                  · linarith only [h6688, h6774, hlam]
                                  · linarith only [h6691, h6774, hlam]
                              · linarith only [h6689, h6771, hlam]
                            · linarith only [h6687, h6770, hlam]
                          · linarith only [h2, h6769, hlam]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          rcases p6699_3 (m.d 0 1) (by simp) with h6780 | h6780
                          · rcases p6699_3 (m.d 1 2) (by simp) with h6781 | h6781
                            · rcases p6699_3 (m.d 1 3) (by simp) with h6782 | h6782
                              · rcases p6699_3 (m.d 1 4) (by simp) with h6783 | h6783
                                · linarith only [h6687, h6783, hlam]
                                · rcases p6699_3 (m.d 1 5) (by simp) with h6785 | h6785
                                  · linarith only [h6688, h6785, hlam]
                                  · rcases h3bigk with h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c | h6787c
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [hlam, p6787_0]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [h1, h6685, h6688, h6693, h6695, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6699_1, p6787_1]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [h4, hlam, p6787_1]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      rcases p6787_3 (m.d 0 3) (by simp) with h6791 | h6791
                                      · rcases p6787_3 (m.d 1 3) (by simp) with h6792 | h6792
                                        · linarith only [h1, h6792, hlam]
                                        · linarith only [h6689, h6792, hlam]
                                      · linarith only [h6791, hlam, p6787_0]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      rcases p6787_3 (m.d 0 3) (by simp) with h6796 | h6796
                                      · rcases p6787_3 (m.d 1 3) (by simp) with h6797 | h6797
                                        · linarith only [h1, h6797, hlam]
                                        · linarith only [h6690, h6797, hlam]
                                      · linarith only [h6796, hlam, p6787_0]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [h1, hlam, p6787_0]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [hlam, p6787_0]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [h6685, hlam, p6787_1]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6787_1]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [h1, hc01, hc35, hlam, hphi, ht0b, ht5b, p6787_1]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [h0, h4, h6688, h6693, h6695, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6699_1, p6787_1]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [h6685, h6688, h6693, h6695, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6699_1, p6787_1]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [hlam, p6787_0]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      rcases p6787_3 (m.d 0 3) (by simp) with h6809 | h6809
                                      · linarith only [h4, h6809, hlam]
                                      · linarith only [h6365, h6809, hlam]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      rcases p6787_3 (m.d 0 3) (by simp) with h6812 | h6812
                                      · linarith only [h4, h6812, hlam]
                                      · linarith only [h6366, h6812, hlam]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [h6365, hlam, p6787_0]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [h6689, hlam, p6787_0]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [h6693, hlam, p6787_0]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [hlam, p6787_0]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [h6697, hlam, p6787_1]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [h6366, hlam, p6787_0]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [h6690, hlam, p6787_0]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [h6694, hlam, p6787_0]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [h6366, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p6787_1]
                                    · have p6787_0 := h6787c.1
                                      have p6787_1 := h6787c.2.1
                                      have p6787_2 := h6787c.2.2.1
                                      have p6787_3 := h6787c.2.2.2
                                      linarith only [hlam, p6787_0]
                              · linarith only [h6690, h6782, hlam]
                            · linarith only [h6688, h6781, hlam]
                          · linarith only [h3, h6780, hlam]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          linarith only [h1, hlam, p6699_0]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          linarith only [h1, h6687, h6693, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6699_1]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          linarith only [hlam, p6699_0]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          rcases p6699_3 (m.d 0 1) (by simp) with h6831 | h6831
                          · rcases p6699_3 (m.d 1 2) (by simp) with h6832 | h6832
                            · linarith only [h6685, h6832, hlam]
                            · linarith only [h6687, h6832, hlam]
                          · linarith only [h2, h6831, hlam]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          rcases p6699_3 (m.d 0 1) (by simp) with h6836 | h6836
                          · rcases p6699_3 (m.d 1 2) (by simp) with h6837 | h6837
                            · linarith only [h6685, h6837, hlam]
                            · linarith only [h6688, h6837, hlam]
                          · linarith only [h3, h6836, hlam]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          linarith only [h2, hlam, p6699_0]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          linarith only [h6687, hlam, p6699_1]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          linarith only [h6689, hlam, p6699_0]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          linarith only [hlam, p6699_0]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          linarith only [h6691, hlam, p6699_1]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          linarith only [h3, hlam, p6699_0]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          linarith only [h6688, hlam, p6699_1]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          linarith only [h6690, hlam, p6699_0]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          rcases p6699_3 (m.d 0 1) (by simp) with h6849 | h6849
                          · rcases p6699_3 (m.d 1 2) (by simp) with h6850 | h6850
                            · rcases p6699_3 (m.d 1 3) (by simp) with h6851 | h6851
                              · rcases p6699_3 (m.d 1 4) (by simp) with h6852 | h6852
                                · linarith only [h6691, h6852, hlam]
                                · rcases p6699_3 (m.d 1 5) (by simp) with h6854 | h6854
                                  · rcases h3bigk with h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c | h6855c
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [hlam, p6855_0]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [h4, h6685, hc12, hc23, hlam, hphi, p6855_1]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [h4, hlam, p6855_1]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      rcases p6855_3 (m.d 0 3) (by simp) with h6859 | h6859
                                      · rcases p6855_3 (m.d 1 3) (by simp) with h6860 | h6860
                                        · linarith only [h1, h6860, hlam]
                                        · linarith only [h6689, h6860, hlam]
                                      · linarith only [h6859, hlam, p6855_0]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      rcases p6855_3 (m.d 0 3) (by simp) with h6864 | h6864
                                      · rcases p6855_3 (m.d 1 3) (by simp) with h6865 | h6865
                                        · linarith only [h1, h6865, hlam]
                                        · linarith only [h6690, h6865, hlam]
                                      · linarith only [h6864, hlam, p6855_0]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [h1, hlam, p6855_0]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [hlam, p6855_0]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [h6685, hlam, p6855_1]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6855_1]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [h1, h6697, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6855_1]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [h4, hc02, hc23, hlam, hphi, p6855_1]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [h6685, h6687, h6688, h6693, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6699_1, p6855_1]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [hlam, p6855_0]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      rcases p6855_3 (m.d 0 3) (by simp) with h6877 | h6877
                                      · linarith only [h4, h6877, hlam]
                                      · linarith only [h6365, h6877, hlam]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      rcases p6855_3 (m.d 0 3) (by simp) with h6880 | h6880
                                      · linarith only [h4, h6880, hlam]
                                      · linarith only [h6366, h6880, hlam]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [h6365, hlam, p6855_0]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [h6689, hlam, p6855_0]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [h6693, hlam, p6855_0]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [hlam, p6855_0]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [h6697, hlam, p6855_1]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [h6366, hlam, p6855_0]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [h6690, hlam, p6855_0]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [h6694, hlam, p6855_0]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [h6366, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p6855_1]
                                    · have p6855_0 := h6855c.1
                                      have p6855_1 := h6855c.2.1
                                      have p6855_2 := h6855c.2.2.1
                                      have p6855_3 := h6855c.2.2.2
                                      linarith only [hlam, p6855_0]
                                  · linarith only [h6691, h6854, hlam]
                              · linarith only [h6689, h6851, hlam]
                            · linarith only [h6687, h6850, hlam]
                          · linarith only [h2, h6849, hlam]
                        · have p6699_0 := h6699c.1
                          have p6699_1 := h6699c.2.1
                          have p6699_2 := h6699c.2.2.1
                          have p6699_3 := h6699c.2.2.2
                          linarith only [hlam, p6699_0]
                  · linarith only [h1, h4, h6690, h6694, hlam]
                · linarith only [h4, h6365, h6693, hlam]
            · linarith only [h6685, h6688, h6690, hlam]
          · linarith only [h6365, h6367, h6685, h6687, h6689, hc24, hc45, hlam, hphi]
        · rcases m.htr 1 3 4 (by decide) (by decide) with h6902 | h6902
          · rcases m.htr 1 3 5 (by decide) (by decide) with h6903 | h6903
            · rcases m.htr 1 4 5 (by decide) (by decide) with h6904 | h6904
              · linarith only [h2, h6367, h6904, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h6906 | h6906
                · rcases m.htr 2 3 5 (by decide) (by decide) with h6907 | h6907
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h6908 | h6908
                    · linarith only [h2, h6367, h6687, h6688, h6908, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h6910 | h6910
                      · linarith only [h6687, h6688, h6906, h6908, h6910, hlam]
                      · rcases h1bigk with h6912c | h6912c | h6912c | h6912c | h6912c | h6912c | h6912c | h6912c | h6912c | h6912c | h6912c | h6912c | h6912c | h6912c | h6912c | h6912c | h6912c | h6912c | h6912c | h6912c | h6912c | h6912c | h6912c | h6912c | h6912c
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          linarith only [hlam, p6912_0]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          rcases p6912_3 (m.d 0 1) (by simp) with h6914 | h6914
                          · rcases p6912_3 (m.d 1 2) (by simp) with h6915 | h6915
                            · linarith only [h6915, hlam, p6912_0]
                            · rcases p6912_3 (m.d 1 3) (by simp) with h6917 | h6917
                              · linarith only [h1, h6917, hlam]
                              · linarith only [h6685, h6917, hlam]
                          · linarith only [h6914, hlam, p6912_0]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          rcases p6912_3 (m.d 0 1) (by simp) with h6921 | h6921
                          · rcases p6912_3 (m.d 1 2) (by simp) with h6922 | h6922
                            · linarith only [h0, h6922, hlam]
                            · rcases p6912_3 (m.d 1 3) (by simp) with h6924 | h6924
                              · linarith only [h6924, hlam, p6912_0]
                              · rcases p6912_3 (m.d 1 4) (by simp) with h6926 | h6926
                                · linarith only [h2, h6926, hlam]
                                · rcases p6912_3 (m.d 1 5) (by simp) with h6928 | h6928
                                  · linarith only [h3, h6928, hlam]
                                  · rcases h3bigk with h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c | h6930c
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h4, h6687, h6688, h6903, h6906, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h4, hlam, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      rcases p6930_3 (m.d 0 3) (by simp) with h6934 | h6934
                                      · rcases p6930_3 (m.d 1 3) (by simp) with h6935 | h6935
                                        · linarith only [h1, h6935, hlam]
                                        · linarith only [h6902, h6935, hlam]
                                      · linarith only [h6934, hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      rcases p6930_3 (m.d 0 3) (by simp) with h6939 | h6939
                                      · rcases p6930_3 (m.d 1 3) (by simp) with h6940 | h6940
                                        · linarith only [h1, h6940, hlam]
                                        · linarith only [h6903, h6940, hlam]
                                      · linarith only [h6939, hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h1, hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6685, hlam, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6912_1, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [hc01, hc35, hlam, hphi, ht0b, ht5b, p6912_1, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h0, h4, h6687, h6906, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6685, h6687, h6906, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      rcases p6930_3 (m.d 0 3) (by simp) with h6952 | h6952
                                      · linarith only [h4, h6952, hlam]
                                      · linarith only [h6365, h6952, hlam]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      rcases p6930_3 (m.d 0 3) (by simp) with h6955 | h6955
                                      · linarith only [h4, h6955, hlam]
                                      · linarith only [h6366, h6955, hlam]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6365, hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6902, hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6906, hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6910, hlam, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6366, hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6903, hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6907, hlam, p6930_0]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [h6366, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p6930_1]
                                    · have p6930_0 := h6930c.1
                                      have p6930_1 := h6930c.2.1
                                      have p6930_2 := h6930c.2.2.1
                                      have p6930_3 := h6930c.2.2.2
                                      linarith only [hlam, p6930_0]
                          · linarith only [h6921, hlam, p6912_0]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          rcases p6912_3 (m.d 0 1) (by simp) with h6969 | h6969
                          · rcases p6912_3 (m.d 1 2) (by simp) with h6970 | h6970
                            · linarith only [h0, h6970, hlam]
                            · linarith only [h6687, h6970, hlam]
                          · linarith only [h6969, hlam, p6912_0]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          rcases p6912_3 (m.d 0 1) (by simp) with h6974 | h6974
                          · rcases p6912_3 (m.d 1 2) (by simp) with h6975 | h6975
                            · linarith only [h0, h6975, hlam]
                            · rcases p6912_3 (m.d 1 3) (by simp) with h6977 | h6977
                              · linarith only [h1, h6977, hlam]
                              · linarith only [h6903, h6977, hlam]
                          · linarith only [h6974, hlam, p6912_0]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          linarith only [h0, hlam, p6912_0]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          linarith only [hlam, p6912_0]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          linarith only [h6685, hlam, p6912_0]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          linarith only [h6688, h6908, hc14, hc45, hlam, hphi, p6912_1]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          linarith only [h6688, hlam, p6912_0]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          linarith only [h1, hlam, p6912_0]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          linarith only [h1, h6687, h6906, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6912_1]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          linarith only [hlam, p6912_0]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          rcases p6912_3 (m.d 0 1) (by simp) with h6989 | h6989
                          · rcases p6912_3 (m.d 1 2) (by simp) with h6990 | h6990
                            · linarith only [h6685, h6990, hlam]
                            · linarith only [h6687, h6990, hlam]
                          · linarith only [h2, h6989, hlam]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          linarith only [h1, h6687, h6688, h6906, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6912_1]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          linarith only [h2, hlam, p6912_0]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          linarith only [h6687, hlam, p6912_1]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          linarith only [h6902, hlam, p6912_0]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          linarith only [hlam, p6912_0]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          linarith only [h6904, hlam, p6912_1]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          linarith only [h3, hlam, p6912_0]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          linarith only [h3, h6687, h6906, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6912_1]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          linarith only [h6903, hlam, p6912_0]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          rcases p6912_3 (m.d 0 1) (by simp) with h7003 | h7003
                          · rcases p6912_3 (m.d 1 2) (by simp) with h7004 | h7004
                            · linarith only [h6688, h7004, hlam]
                            · linarith only [h6687, h7004, hlam]
                          · linarith only [h2, h7003, hlam]
                        · have p6912_0 := h6912c.1
                          have p6912_1 := h6912c.2.1
                          have p6912_2 := h6912c.2.2.1
                          have p6912_3 := h6912c.2.2.2
                          linarith only [hlam, p6912_0]
                  · linarith only [h1, h4, h6903, h6907, hlam]
                · linarith only [h4, h6365, h6906, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h7011 | h7011
              · linarith only [h2, h6367, h7011, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7013 | h7013
                · rcases m.htr 2 3 5 (by decide) (by decide) with h7014 | h7014
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h7015 | h7015
                    · linarith only [h6366, h6367, h6685, h6687, h6903, h7015, hlam]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h7017 | h7017
                      · linarith only [h4, h6366, h6685, h6687, h6903, h7013, h7015, h7017, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases h1bigk with h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c | h7019c
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [hlam, p7019_0]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          rcases p7019_3 (m.d 0 1) (by simp) with h7021 | h7021
                          · rcases p7019_3 (m.d 1 2) (by simp) with h7022 | h7022
                            · linarith only [h7022, hlam, p7019_0]
                            · rcases p7019_3 (m.d 1 3) (by simp) with h7024 | h7024
                              · linarith only [h1, h7024, hlam]
                              · linarith only [h6685, h7024, hlam]
                          · linarith only [h7021, hlam, p7019_0]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          rcases p7019_3 (m.d 0 1) (by simp) with h7028 | h7028
                          · rcases p7019_3 (m.d 1 2) (by simp) with h7029 | h7029
                            · linarith only [h0, h7029, hlam]
                            · rcases p7019_3 (m.d 1 3) (by simp) with h7031 | h7031
                              · linarith only [h7031, hlam, p7019_0]
                              · rcases p7019_3 (m.d 1 4) (by simp) with h7033 | h7033
                                · linarith only [h2, h7033, hlam]
                                · rcases p7019_3 (m.d 1 5) (by simp) with h7035 | h7035
                                  · linarith only [h3, h7035, hlam]
                                  · linarith only [h6903, h7035, hlam]
                          · linarith only [h7028, hlam, p7019_0]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          rcases p7019_3 (m.d 0 1) (by simp) with h7039 | h7039
                          · rcases p7019_3 (m.d 1 2) (by simp) with h7040 | h7040
                            · linarith only [h0, h7040, hlam]
                            · linarith only [h6687, h7040, hlam]
                          · linarith only [h7039, hlam, p7019_0]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          rcases p7019_3 (m.d 0 1) (by simp) with h7044 | h7044
                          · rcases p7019_3 (m.d 1 2) (by simp) with h7045 | h7045
                            · linarith only [h0, h7045, hlam]
                            · rcases p7019_3 (m.d 1 3) (by simp) with h7047 | h7047
                              · linarith only [h1, h7047, hlam]
                              · rcases p7019_3 (m.d 1 4) (by simp) with h7049 | h7049
                                · linarith only [h2, h7049, hlam]
                                · rcases p7019_3 (m.d 1 5) (by simp) with h7051 | h7051
                                  · linarith only [h7051, hlam, p7019_0]
                                  · rcases h3bigk with h7053c | h7053c | h7053c | h7053c | h7053c | h7053c | h7053c | h7053c | h7053c | h7053c | h7053c | h7053c | h7053c | h7053c | h7053c | h7053c | h7053c | h7053c | h7053c | h7053c | h7053c | h7053c | h7053c | h7053c | h7053c
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [hlam, p7053_0]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [h4, h6685, hc12, hc23, hlam, hphi, p7053_1]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [h4, hlam, p7053_1]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      rcases p7053_3 (m.d 0 3) (by simp) with h7057 | h7057
                                      · rcases p7053_3 (m.d 1 3) (by simp) with h7058 | h7058
                                        · linarith only [h1, h7058, hlam]
                                        · linarith only [h6902, h7058, hlam]
                                      · linarith only [h7057, hlam, p7053_0]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [h4, h6685, h6687, h6903, h7013, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7053_1]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [h1, hlam, p7053_0]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [hlam, p7053_0]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [h6685, hlam, p7053_1]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [h1, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7053_1]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [h6903, hlam, p7053_0]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [h4, hc02, hc23, hlam, hphi, p7053_1]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [h6685, h6687, h7013, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7053_1]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [hlam, p7053_0]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      rcases p7053_3 (m.d 0 3) (by simp) with h7071 | h7071
                                      · linarith only [h4, h7071, hlam]
                                      · linarith only [h6365, h7071, hlam]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [h6685, h6687, h6903, h7013, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7053_1]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [h6365, hlam, p7053_0]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [h6902, hlam, p7053_0]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [h7013, hlam, p7053_0]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [hlam, p7053_0]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [h7017, hlam, p7053_1]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [h6366, hlam, p7053_0]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [h6366, h6685, h6687, h7013, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p7053_1]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [h7014, hlam, p7053_0]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [h4, h6366, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7053_1]
                                    · have p7053_0 := h7053c.1
                                      have p7053_1 := h7053c.2.1
                                      have p7053_2 := h7053c.2.2.1
                                      have p7053_3 := h7053c.2.2.2
                                      linarith only [hlam, p7053_0]
                          · linarith only [h7044, hlam, p7019_0]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [h0, hlam, p7019_0]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [hlam, p7019_0]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [h6685, hlam, p7019_0]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [h4, h6366, h6685, h6687, h6903, h7013, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7019_1]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [h6688, hlam, p7019_0]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [h1, hlam, p7019_0]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [h1, h6687, h7013, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p7019_1]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [hlam, p7019_0]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [h4, h6366, h6687, h6903, h7013, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7019_1]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [h6903, hlam, p7019_1]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [h2, hlam, p7019_0]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [h6687, hlam, p7019_1]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [h6902, hlam, p7019_0]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [hlam, p7019_0]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [h7011, hlam, p7019_1]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [h3, hlam, p7019_0]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [h3, h6367, h6687, h7013, hc34, hc45, hlam, hphi, p7019_1]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [h4, h6366, h6685, h6687, h6903, h7013, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p7019_1]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          rcases p7019_3 (m.d 0 1) (by simp) with h7104 | h7104
                          · rcases p7019_3 (m.d 1 2) (by simp) with h7105 | h7105
                            · linarith only [h6688, h7105, hlam]
                            · linarith only [h6687, h7105, hlam]
                          · linarith only [h2, h7104, hlam]
                        · have p7019_0 := h7019c.1
                          have p7019_1 := h7019c.2.1
                          have p7019_2 := h7019c.2.2.1
                          have p7019_3 := h7019c.2.2.2
                          linarith only [hlam, p7019_0]
                  · linarith only [h4, h6366, h7014, hlam]
                · linarith only [h4, h6365, h7013, hlam]
          · linarith only [h6365, h6367, h6685, h6687, h6902, hc24, hc45, hlam, hphi]
      · linarith only [h4, h6364, h6687, hc12, hc23, hlam, hphi]

end R2N4
