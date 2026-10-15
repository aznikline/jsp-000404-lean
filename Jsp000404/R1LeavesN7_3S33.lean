import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11016000 in
set_option maxHeartbeats 11016000 in
theorem r1l7_11_13_25_L_I_L_I_H_I_s16_x1_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg14799 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg16563 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg17994 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h19110 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h22593 : (m.d 2 4 + m.lam ≤ m.d 0 2 ∧ m.d 2 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 2))
    (h23332 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have h5bigk := hb5.1
  have h0 := hg0
  have h14799 := hg14799
  have h16563 := hg16563
  have h17994 := hg17994
  rcases m.htr 0 3 4 (by decide) (by decide) with h23333 | h23333
  · rcases m.htr 0 3 5 (by decide) (by decide) with h23334 | h23334
    · rcases m.htr 0 4 5 (by decide) (by decide) with h23335 | h23335
      · rcases m.htr 1 2 3 (by decide) (by decide) with h23336 | h23336
        · rcases m.htr 1 2 4 (by decide) (by decide) with h23337 | h23337
          · rcases m.htr 1 2 5 (by decide) (by decide) with h23338 | h23338
            · rcases m.htr 1 3 4 (by decide) (by decide) with h23339 | h23339
              · rcases m.htr 1 3 5 (by decide) (by decide) with h23340 | h23340
                · rcases m.htr 1 4 5 (by decide) (by decide) with h23341 | h23341
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h23342 | h23342
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h23343 | h23343
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h23344 | h23344
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h23345 | h23345
                          · rcases h1bigk with h23346c | h23346c | h23346c | h23346c | h23346c | h23346c | h23346c | h23346c | h23346c | h23346c | h23346c | h23346c | h23346c | h23346c | h23346c | h23346c | h23346c | h23346c | h23346c | h23346c | h23346c | h23346c | h23346c | h23346c | h23346c
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [hlam, p23346_0]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [h0, hlam, p23346_0]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [h14799, hlam, p23346_0]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [h16563, hlam, p23346_0]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [h17994, hlam, p23346_0]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              rcases p23346_3 (m.d 0 1) (by simp) with h23352 | h23352
                              · linarith only [h23352, hlam, p23346_0]
                              · rcases p23346_3 (m.d 1 2) (by simp) with h23354 | h23354
                                · rcases p23346_3 (m.d 1 3) (by simp) with h23355 | h23355
                                  · linarith only [h23336, h23355, hlam]
                                  · linarith only [h14799, h23355, hlam]
                                · linarith only [h23354, hlam, p23346_0]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [hlam, p23346_0]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [h22593, h23332, h23337, h23339, h23343, h23345, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23346_1]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [h22593, h23332, h23337, h23343, h23345, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23346_1]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [h17994, hc01, hc12, hlam, hphi, p23346_1]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              rcases p23346_3 (m.d 0 1) (by simp) with h23363 | h23363
                              · linarith only [h23363, hlam, p23346_0]
                              · rcases p23346_3 (m.d 1 2) (by simp) with h23365 | h23365
                                · rcases p23346_3 (m.d 1 3) (by simp) with h23366 | h23366
                                  · rcases p23346_3 (m.d 1 4) (by simp) with h23367 | h23367
                                    · linarith only [h23339, h23367, hlam]
                                    · linarith only [h16563, h23367, hlam]
                                  · linarith only [h23366, hlam, p23346_0]
                                · linarith only [h0, h23365, hlam]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [h23336, hlam, p23346_1]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [hlam, p23346_0]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [h22593, h23332, h23337, h23343, h23345, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p23346_1]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [h17994, h23336, hc01, hc12, hlam, hphi, p23346_1]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              rcases p23346_3 (m.d 0 1) (by simp) with h23376 | h23376
                              · linarith only [h23376, hlam, p23346_0]
                              · rcases p23346_3 (m.d 1 2) (by simp) with h23378 | h23378
                                · rcases p23346_3 (m.d 1 3) (by simp) with h23379 | h23379
                                  · rcases p23346_3 (m.d 1 4) (by simp) with h23380 | h23380
                                    · rcases p23346_3 (m.d 1 5) (by simp) with h23381 | h23381
                                      · linarith only [h23341, h23381, hlam]
                                      · linarith only [h17994, h23381, hlam]
                                    · linarith only [h23380, hlam, p23346_0]
                                  · linarith only [h14799, h23379, hlam]
                                · linarith only [h0, h23378, hlam]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [h23337, hlam, p23346_1]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [h23339, hlam, p23346_0]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [hlam, p23346_0]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [h17994, hc01, hc14, hlam, hphi, p23346_1]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              rcases p23346_3 (m.d 0 1) (by simp) with h23391 | h23391
                              · linarith only [h23391, hlam, p23346_0]
                              · rcases p23346_3 (m.d 1 2) (by simp) with h23393 | h23393
                                · rcases p23346_3 (m.d 1 3) (by simp) with h23394 | h23394
                                  · rcases p23346_3 (m.d 1 4) (by simp) with h23395 | h23395
                                    · rcases p23346_3 (m.d 1 5) (by simp) with h23396 | h23396
                                      · rcases h3bigk with h23397c | h23397c | h23397c | h23397c | h23397c | h23397c | h23397c | h23397c | h23397c | h23397c | h23397c | h23397c | h23397c | h23397c | h23397c | h23397c | h23397c | h23397c | h23397c | h23397c | h23397c | h23397c | h23397c | h23397c | h23397c
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [hlam, p23397_0]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [h14799, hlam, p23397_1]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [h19110, hlam, p23397_1]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [h19110, h23336, h23345, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23397_1]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          rcases p23397_3 (m.d 0 3) (by simp) with h23402 | h23402
                                          · rcases p23397_3 (m.d 1 3) (by simp) with h23403 | h23403
                                            · rcases p23397_3 (m.d 2 3) (by simp) with h23404 | h23404
                                              · rcases p23397_3 (m.d 3 4) (by simp) with h23405 | h23405
                                                · linarith only [h23333, h23405, hlam]
                                                · linarith only [h23345, h23405, hlam]
                                              · linarith only [h23343, h23404, hlam]
                                            · linarith only [h23340, h23403, hlam]
                                          · linarith only [h23402, hlam, p23397_0]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [h23333, h23336, h23345, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23397_1]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [hlam, p23397_0]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [h19110, h23332, h23336, h23343, h23345, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23397_1]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          rcases p23397_3 (m.d 0 3) (by simp) with h23414 | h23414
                                          · linarith only [h14799, h23414, hlam]
                                          · linarith only [h23333, h23414, hlam]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          rcases p23397_3 (m.d 0 3) (by simp) with h23417 | h23417
                                          · linarith only [h14799, h23417, hlam]
                                          · linarith only [h23334, h23417, hlam]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [h23333, h23345, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p23397_1]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [h23336, hlam, p23397_0]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [hlam, p23397_0]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [h23336, h23345, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23397_1]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          rcases p23397_3 (m.d 0 3) (by simp) with h23424 | h23424
                                          · linarith only [h19110, h23424, hlam]
                                          · linarith only [h23334, h23424, hlam]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [h23333, hlam, p23397_0]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [h23339, hlam, p23397_0]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [h23342, hlam, p23397_0]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [hlam, p23397_0]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [h19110, h23333, h23336, h23345, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p23397_1]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [h23334, hlam, p23397_0]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [h23340, hlam, p23397_0]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [h23343, hlam, p23397_0]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [h23345, hlam, p23397_0]
                                        · have p23397_0 := h23397c.1
                                          have p23397_1 := h23397c.2.1
                                          have p23397_2 := h23397c.2.2.1
                                          have p23397_3 := h23397c.2.2.2
                                          linarith only [hlam, p23397_0]
                                      · linarith only [h23396, hlam, p23346_0]
                                    · linarith only [h16563, h23395, hlam]
                                  · linarith only [h14799, h23394, hlam]
                                · linarith only [h0, h23393, hlam]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [h23338, hlam, p23346_1]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [h23340, hlam, p23346_0]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [h23341, hlam, p23346_0]
                            · have p23346_0 := h23346c.1
                              have p23346_1 := h23346c.2.1
                              have p23346_2 := h23346c.2.2.1
                              have p23346_3 := h23346c.2.2.2
                              linarith only [hlam, p23346_0]
                          · linarith only [h22593, h23332, h23336, h23342, h23344, h23345, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                        · linarith only [h19110, h22593, h23333, h23335, h23336, h23344, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                      · linarith only [h19110, h23334, h23343, hlam]
                    · linarith only [h19110, h23333, h23342, hlam]
                  · linarith only [h16563, h19110, h23332, h23335, h23341, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h14799, h23334, h23340, hlam]
              · linarith only [h14799, h19110, h23333, h23336, h23339, hc01, hc12, hlam, hphi]
            · linarith only [h19110, h23336, h23338, hc02, hc25, hlam, hphi]
          · linarith only [h17994, h19110, h23332, h23336, h23337, hc01, hc24, hlam, hphi, ht12]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h23454 | h23454
          · linarith only [h17994, h22593, h23332, h23336, h23454, hc01, hc23, hlam, hphi, ht12]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h23456 | h23456
            · rcases m.htr 1 3 4 (by decide) (by decide) with h23457 | h23457
              · rcases m.htr 1 3 5 (by decide) (by decide) with h23458 | h23458
                · rcases m.htr 1 4 5 (by decide) (by decide) with h23459 | h23459
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h23460 | h23460
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h23461 | h23461
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h23462 | h23462
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h23463 | h23463
                          · rcases h1bigk with h23464c | h23464c | h23464c | h23464c | h23464c | h23464c | h23464c | h23464c | h23464c | h23464c | h23464c | h23464c | h23464c | h23464c | h23464c | h23464c | h23464c | h23464c | h23464c | h23464c | h23464c | h23464c | h23464c | h23464c | h23464c
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [hlam, p23464_0]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [h0, hlam, p23464_0]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [h14799, hlam, p23464_0]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [h16563, hlam, p23464_0]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [h17994, hlam, p23464_0]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [h23454, h23460, hc01, hc23, hlam, hphi, ht12, p23464_1]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [hlam, p23464_0]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [h23336, hlam, p23464_0]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [h23454, hlam, p23464_0]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [h17994, h23454, h23460, hc01, hc23, hlam, hphi, ht12, p23464_1]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              rcases p23464_3 (m.d 0 1) (by simp) with h23475 | h23475
                              · linarith only [h23475, hlam, p23464_0]
                              · rcases p23464_3 (m.d 1 2) (by simp) with h23477 | h23477
                                · linarith only [h23336, h23477, hlam]
                                · linarith only [h0, h23477, hlam]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [h0, h23336, hc01, hc23, hlam, hphi, ht12, p23464_1]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [hlam, p23464_0]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [h17994, h23336, h23454, h23456, hc01, hc23, hlam, hphi, ht12, p23464_1]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [h17994, h23336, hc01, hc23, hlam, hphi, ht12, p23464_1]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              rcases p23464_3 (m.d 0 1) (by simp) with h23484 | h23484
                              · linarith only [h23484, hlam, p23464_0]
                              · rcases p23464_3 (m.d 1 2) (by simp) with h23486 | h23486
                                · linarith only [h23454, h23486, hlam]
                                · linarith only [h0, h23486, hlam]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [h17994, h23456, hc01, hc14, hlam, hphi, p23464_1]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [h23457, hlam, p23464_0]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [hlam, p23464_0]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [h17994, h23454, h23460, hc01, hc23, hlam, hphi, ht12, p23464_1]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [h23336, h23456, hc01, hc23, hlam, hphi, ht12, p23464_1]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [h23456, hlam, p23464_1]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [h23458, hlam, p23464_0]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [h23459, hlam, p23464_0]
                            · have p23464_0 := h23464c.1
                              have p23464_1 := h23464c.2.1
                              have p23464_2 := h23464c.2.2.1
                              have p23464_3 := h23464c.2.2.2
                              linarith only [hlam, p23464_0]
                          · rcases h1bigk with h23498c | h23498c | h23498c | h23498c | h23498c | h23498c | h23498c | h23498c | h23498c | h23498c | h23498c | h23498c | h23498c | h23498c | h23498c | h23498c | h23498c | h23498c | h23498c | h23498c | h23498c | h23498c | h23498c | h23498c | h23498c
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [hlam, p23498_0]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [h0, hlam, p23498_0]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [h14799, hlam, p23498_0]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [h16563, hlam, p23498_0]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [h17994, hlam, p23498_0]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [h23454, h23460, hc01, hc23, hlam, hphi, ht12, p23498_1]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [hlam, p23498_0]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [h23336, hlam, p23498_0]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [h23454, hlam, p23498_0]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [h17994, h23454, h23460, hc01, hc23, hlam, hphi, ht12, p23498_1]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              rcases p23498_3 (m.d 0 1) (by simp) with h23509 | h23509
                              · linarith only [h23509, hlam, p23498_0]
                              · rcases p23498_3 (m.d 1 2) (by simp) with h23511 | h23511
                                · linarith only [h23336, h23511, hlam]
                                · linarith only [h0, h23511, hlam]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [h0, h23336, hc01, hc23, hlam, hphi, ht12, p23498_1]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [hlam, p23498_0]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [h16563, h23336, hc01, hc23, hlam, hphi, ht12, p23498_1]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [h17994, h23336, hc01, hc23, hlam, hphi, ht12, p23498_1]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              rcases p23498_3 (m.d 0 1) (by simp) with h23518 | h23518
                              · linarith only [h23518, hlam, p23498_0]
                              · rcases p23498_3 (m.d 1 2) (by simp) with h23520 | h23520
                                · linarith only [h23454, h23520, hlam]
                                · linarith only [h0, h23520, hlam]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [h0, h23332, h23462, h23463, hc14, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p23498_1]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [h23457, hlam, p23498_0]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [hlam, p23498_0]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [h17994, h23454, h23460, hc01, hc23, hlam, hphi, ht12, p23498_1]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [h23336, h23456, hc01, hc23, hlam, hphi, ht12, p23498_1]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [h23456, hlam, p23498_1]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [h23458, hlam, p23498_0]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [h23459, hlam, p23498_0]
                            · have p23498_0 := h23498c.1
                              have p23498_1 := h23498c.2.1
                              have p23498_2 := h23498c.2.2.1
                              have p23498_3 := h23498c.2.2.2
                              linarith only [hlam, p23498_0]
                        · linarith only [h0, h23454, h23462, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h14799, h23334, h23336, h23461, hlam]
                    · linarith only [h17994, h23336, h23456, h23460, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h16563, h23335, h23459, hlam]
                · linarith only [h0, h14799, h23332, h23334, h23336, h23458, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h14799, h23333, h23457, hlam]
            · linarith only [h0, h23332, h23456, hlam]
      · linarith only [h22593, h23332, h23335, hlam]
    · linarith only [h22593, h23332, h23333, h23334, hlam]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h23541 | h23541
    · rcases m.htr 0 4 5 (by decide) (by decide) with h23542 | h23542
      · rcases m.htr 1 2 3 (by decide) (by decide) with h23543 | h23543
        · rcases m.htr 1 2 4 (by decide) (by decide) with h23544 | h23544
          · rcases m.htr 1 2 5 (by decide) (by decide) with h23545 | h23545
            · rcases m.htr 1 3 4 (by decide) (by decide) with h23546 | h23546
              · rcases m.htr 1 3 5 (by decide) (by decide) with h23547 | h23547
                · rcases m.htr 1 4 5 (by decide) (by decide) with h23548 | h23548
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h23549 | h23549
                    · linarith only [h19110, h23332, h23333, h23543, h23549, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h19110, h23332, h23543, h23546, h23549, hc12, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h16563, h23542, h23548, hlam]
                · linarith only [h14799, h23541, h23547, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h23554 | h23554
                · rcases m.htr 1 4 5 (by decide) (by decide) with h23555 | h23555
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h23556 | h23556
                    · linarith only [h23543, h23546, h23556, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h23558 | h23558
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h23559 | h23559
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h23560 | h23560
                          · rcases h1bigk with h23561c | h23561c | h23561c | h23561c | h23561c | h23561c | h23561c | h23561c | h23561c | h23561c | h23561c | h23561c | h23561c | h23561c | h23561c | h23561c | h23561c | h23561c | h23561c | h23561c | h23561c | h23561c | h23561c | h23561c | h23561c
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [hlam, p23561_0]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [h0, hlam, p23561_0]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [h14799, hlam, p23561_0]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [h16563, hlam, p23561_0]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [h17994, hlam, p23561_0]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              rcases p23561_3 (m.d 0 1) (by simp) with h23567 | h23567
                              · linarith only [h23567, hlam, p23561_0]
                              · rcases p23561_3 (m.d 1 2) (by simp) with h23569 | h23569
                                · rcases p23561_3 (m.d 1 3) (by simp) with h23570 | h23570
                                  · linarith only [h23543, h23570, hlam]
                                  · linarith only [h14799, h23570, hlam]
                                · linarith only [h23569, hlam, p23561_0]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [hlam, p23561_0]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [h14799, hc01, hc12, hlam, hphi, p23561_1]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [h16563, hc01, hc12, hlam, hphi, p23561_1]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [h17994, hc01, hc12, hlam, hphi, p23561_1]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [h23546, hc01, hc34, hlam, hphi, ht12, ht23, p23561_1]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [h23543, hlam, p23561_1]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [hlam, p23561_0]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [h23546, hlam, p23561_1]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [h17994, hc01, hc13, hlam, hphi, p23561_1]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              rcases p23561_3 (m.d 0 1) (by simp) with h23583 | h23583
                              · linarith only [h23583, hlam, p23561_0]
                              · rcases p23561_3 (m.d 1 2) (by simp) with h23585 | h23585
                                · rcases p23561_3 (m.d 1 3) (by simp) with h23586 | h23586
                                  · linarith only [h23546, h23586, hlam]
                                  · linarith only [h14799, h23586, hlam]
                                · linarith only [h0, h23585, hlam]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [h23544, hlam, p23561_1]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [h14799, h23546, hc01, hc34, hlam, hphi, ht12, ht23, p23561_1]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [hlam, p23561_0]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [h17994, h23546, hc01, hc34, hlam, hphi, ht12, ht23, p23561_1]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [h23546, h23554, hc01, hc34, hlam, hphi, ht12, ht23, p23561_1]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [h23545, hlam, p23561_1]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [h23554, hlam, p23561_0]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [h23555, hlam, p23561_0]
                            · have p23561_0 := h23561c.1
                              have p23561_1 := h23561c.2.1
                              have p23561_2 := h23561c.2.2.1
                              have p23561_3 := h23561c.2.2.2
                              linarith only [hlam, p23561_0]
                          · linarith only [h14799, h23546, h23560, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                        · linarith only [h16563, h19110, h22593, h23332, h23542, h23543, h23546, h23559, hc01, hc34, hlam, hphi, ht12, ht23]
                      · linarith only [h19110, h23332, h23333, h23541, h23558, hc04, hc25, hlam, hphi, ht0b, ht5b]
                  · linarith only [h16563, h17994, h23542, h23546, h23554, h23555, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h14799, h22593, h23333, h23541, h23554, hc01, hc24, hlam, hphi, ht12]
            · linarith only [h0, h23332, h23545, hlam]
          · linarith only [h19110, h23543, h23544, hc02, hc24, hlam, hphi]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h23606 | h23606
          · linarith only [h22593, h23332, h23543, h23606, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h23608 | h23608
            · rcases m.htr 1 3 4 (by decide) (by decide) with h23609 | h23609
              · rcases m.htr 1 3 5 (by decide) (by decide) with h23610 | h23610
                · rcases m.htr 1 4 5 (by decide) (by decide) with h23611 | h23611
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h23612 | h23612
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h23613 | h23613
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h23614 | h23614
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h23615 | h23615
                          · rcases h1bigk with h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c | h23616c
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [hlam, p23616_0]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [h0, hlam, p23616_0]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [h14799, hlam, p23616_0]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [h16563, hlam, p23616_0]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [h17994, hlam, p23616_0]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [h23606, h23612, hc01, hc23, hlam, hphi, ht12, p23616_1]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [hlam, p23616_0]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [h23543, hlam, p23616_0]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [h23606, hlam, p23616_0]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [h17994, h23606, h23612, hc01, hc23, hlam, hphi, ht12, p23616_1]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              rcases p23616_3 (m.d 0 1) (by simp) with h23627 | h23627
                              · linarith only [h23627, hlam, p23616_0]
                              · rcases p23616_3 (m.d 1 2) (by simp) with h23629 | h23629
                                · linarith only [h23543, h23629, hlam]
                                · linarith only [h0, h23629, hlam]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [h0, hc01, hc13, hlam, hphi, p23616_1]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [hlam, p23616_0]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [h17994, h23543, h23606, h23608, hc01, hc23, hlam, hphi, ht12, p23616_1]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [h17994, h23543, hc01, hc23, hlam, hphi, ht12, p23616_1]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              rcases p23616_3 (m.d 0 1) (by simp) with h23636 | h23636
                              · linarith only [h23636, hlam, p23616_0]
                              · rcases p23616_3 (m.d 1 2) (by simp) with h23638 | h23638
                                · linarith only [h23606, h23638, hlam]
                                · linarith only [h0, h23638, hlam]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [h17994, h23608, hc01, hc14, hlam, hphi, p23616_1]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [h23609, hlam, p23616_0]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [hlam, p23616_0]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [h17994, h23606, h23612, hc01, hc23, hlam, hphi, ht12, p23616_1]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [h23543, h23608, hc01, hc23, hlam, hphi, ht12, p23616_1]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [h23608, hlam, p23616_1]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [h23610, hlam, p23616_0]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [h23611, hlam, p23616_0]
                            · have p23616_0 := h23616c.1
                              have p23616_1 := h23616c.2.1
                              have p23616_2 := h23616c.2.2.1
                              have p23616_3 := h23616c.2.2.2
                              linarith only [hlam, p23616_0]
                          · linarith only [h19110, h23332, h23333, h23542, h23613, h23615, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h0, h23606, h23614, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                      · linarith only [h19110, h23333, h23543, h23609, h23613, hc02, hc35, hlam, hphi, ht23]
                    · linarith only [h23543, h23609, h23612, hlam]
                  · linarith only [h16563, h23542, h23611, hlam]
                · linarith only [h23333, h23541, h23609, h23610, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h23656 | h23656
                · rcases m.htr 1 4 5 (by decide) (by decide) with h23657 | h23657
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h23658 | h23658
                    · linarith only [h17994, h23543, h23608, h23609, h23658, hc01, hc23, hlam, hphi, ht12]
                    · linarith only [h17994, h23543, h23608, h23658, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h16563, h23332, h23542, h23543, h23657, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h14799, h23541, h23656, hlam]
            · linarith only [h0, h23332, h23608, hlam]
      · linarith only [h19110, h23332, h23333, h23542, hlam]
    · linarith only [h19110, h23332, h23541, hlam]

end R2N4
