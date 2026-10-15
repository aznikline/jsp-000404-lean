import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10776000 in
set_option maxHeartbeats 10776000 in
theorem r1l7_13_24_L_I_H_I_s10_x0_x0 (m : N7Model)
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig2_7_H_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg7360 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg8811 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (h10295 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h10296 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have h3bigk := hb3.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h7360 := hg7360
  have h8811 := hg8811
  rcases m.htr 0 2 4 (by decide) (by decide) with h10297 | h10297
  · rcases m.htr 0 3 4 (by decide) (by decide) with h10298 | h10298
    · rcases m.htr 0 3 5 (by decide) (by decide) with h10299 | h10299
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10300 | h10300
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10301 | h10301
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10302 | h10302
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10303 | h10303
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10304 | h10304
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10305 | h10305
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10306 | h10306
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10307 | h10307
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10308 | h10308
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10309 | h10309
                          · rcases h3bigk with h10310c | h10310c | h10310c | h10310c | h10310c | h10310c | h10310c | h10310c | h10310c | h10310c | h10310c | h10310c | h10310c | h10310c | h10310c | h10310c | h10310c | h10310c | h10310c | h10310c | h10310c | h10310c | h10310c | h10310c | h10310c
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [hlam, p10310_0]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [h7360, hlam, p10310_1]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [h10306, h10309, hc03, hc45, hlam, hphi, ht0b, ht5b, p10310_1]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              rcases p10310_3 (m.d 0 3) (by simp) with h10314 | h10314
                              · rcases p10310_3 (m.d 1 3) (by simp) with h10315 | h10315
                                · rcases p10310_3 (m.d 2 3) (by simp) with h10316 | h10316
                                  · linarith only [h10296, h10316, hlam]
                                  · linarith only [h10306, h10316, hlam]
                                · linarith only [h10303, h10315, hlam]
                              · linarith only [h10314, hlam, p10310_0]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              rcases p10310_3 (m.d 0 3) (by simp) with h10321 | h10321
                              · rcases p10310_3 (m.d 1 3) (by simp) with h10322 | h10322
                                · rcases p10310_3 (m.d 2 3) (by simp) with h10323 | h10323
                                  · linarith only [h10296, h10323, hlam]
                                  · linarith only [h10307, h10323, hlam]
                                · linarith only [h10304, h10322, hlam]
                              · linarith only [h10321, hlam, p10310_0]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [h10296, h10301, h10306, h10309, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10310_1]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [hlam, p10310_0]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [h10301, h10306, h10309, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10310_1]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              rcases p10310_3 (m.d 0 3) (by simp) with h10331 | h10331
                              · linarith only [h10331, h7360, hlam]
                              · linarith only [h10298, h10331, hlam]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              rcases p10310_3 (m.d 0 3) (by simp) with h10334 | h10334
                              · linarith only [h10334, h7360, hlam]
                              · linarith only [h10299, h10334, hlam]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [h10296, hlam, p10310_0]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [h10301, hlam, p10310_0]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [hlam, p10310_0]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [h10296, h10309, hc02, hc45, hlam, hphi, ht0b, ht5b, p10310_1]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              rcases p10310_3 (m.d 0 3) (by simp) with h10341 | h10341
                              · rcases p10310_3 (m.d 1 3) (by simp) with h10342 | h10342
                                · rcases p10310_3 (m.d 2 3) (by simp) with h10343 | h10343
                                  · rcases p10310_3 (m.d 3 4) (by simp) with h10344 | h10344
                                    · linarith only [h10306, h10344, hlam]
                                    · linarith only [h10309, h10344, hlam]
                                  · linarith only [h10343, hlam, p10310_0]
                                · linarith only [h10304, h10342, hlam]
                              · linarith only [h10299, h10341, hlam]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [h10298, hlam, p10310_0]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [h10303, hlam, p10310_0]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [h10306, hlam, p10310_0]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [hlam, p10310_0]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [h0, h10296, h10306, h10309, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10310_1]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [h10299, hlam, p10310_0]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [h10304, hlam, p10310_0]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [h10307, hlam, p10310_0]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [h10309, hlam, p10310_0]
                            · have p10310_0 := h10310c.1
                              have p10310_1 := h10310c.2.1
                              have p10310_2 := h10310c.2.2.1
                              have p10310_3 := h10310c.2.2.2
                              linarith only [hlam, p10310_0]
                          · rcases h3bigk with h10360c | h10360c | h10360c | h10360c | h10360c | h10360c | h10360c | h10360c | h10360c | h10360c | h10360c | h10360c | h10360c | h10360c | h10360c | h10360c | h10360c | h10360c | h10360c | h10360c | h10360c | h10360c | h10360c | h10360c | h10360c
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [hlam, p10360_0]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [h7360, hlam, p10360_1]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [h0, h10296, h10306, h10308, h10309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10360_1]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              rcases p10360_3 (m.d 0 3) (by simp) with h10364 | h10364
                              · rcases p10360_3 (m.d 1 3) (by simp) with h10365 | h10365
                                · rcases p10360_3 (m.d 2 3) (by simp) with h10366 | h10366
                                  · linarith only [h10296, h10366, hlam]
                                  · linarith only [h10306, h10366, hlam]
                                · linarith only [h10303, h10365, hlam]
                              · linarith only [h10364, hlam, p10360_0]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              rcases p10360_3 (m.d 0 3) (by simp) with h10371 | h10371
                              · rcases p10360_3 (m.d 1 3) (by simp) with h10372 | h10372
                                · rcases p10360_3 (m.d 2 3) (by simp) with h10373 | h10373
                                  · linarith only [h10296, h10373, hlam]
                                  · linarith only [h10307, h10373, hlam]
                                · linarith only [h10304, h10372, hlam]
                              · linarith only [h10371, hlam, p10360_0]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [h10295, h10301, h10305, h10309, h7360, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10360_1]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [hlam, p10360_0]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [h10301, h10306, h10308, h10309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10360_1]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [h10295, h10305, h10309, h7360, hlam, p10360_2]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              rcases p10360_3 (m.d 0 3) (by simp) with h10382 | h10382
                              · linarith only [h10382, h7360, hlam]
                              · linarith only [h10299, h10382, hlam]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [h10296, hlam, p10360_0]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [h10301, hlam, p10360_0]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [hlam, p10360_0]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              rcases p10360_3 (m.d 0 3) (by simp) with h10388 | h10388
                              · rcases p10360_3 (m.d 1 3) (by simp) with h10389 | h10389
                                · rcases p10360_3 (m.d 2 3) (by simp) with h10390 | h10390
                                  · rcases p10360_3 (m.d 3 4) (by simp) with h10391 | h10391
                                    · linarith only [h10391, hlam, p10360_0]
                                    · rcases p10360_3 (m.d 3 5) (by simp) with h10393 | h10393
                                      · linarith only [h10307, h10393, hlam]
                                      · linarith only [h10309, h10393, hlam]
                                  · linarith only [h10390, hlam, p10360_0]
                                · linarith only [h10303, h10389, hlam]
                              · linarith only [h10298, h10388, hlam]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              rcases p10360_3 (m.d 0 3) (by simp) with h10399 | h10399
                              · rcases p10360_3 (m.d 1 3) (by simp) with h10400 | h10400
                                · rcases p10360_3 (m.d 2 3) (by simp) with h10401 | h10401
                                  · rcases p10360_3 (m.d 3 4) (by simp) with h10402 | h10402
                                    · linarith only [h10306, h10402, hlam]
                                    · rcases p10360_3 (m.d 3 5) (by simp) with h10404 | h10404
                                      · linarith only [h10404, hlam, p10360_0]
                                      · rcases h4bigk with h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c | h10406c
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [hlam, p10406_0]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [h8811, hlam, p10406_0]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [h10308, h10309, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p10406_1]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          rcases p10406_3 (m.d 0 4) (by simp) with h10410 | h10410
                                          · rcases p10406_3 (m.d 1 4) (by simp) with h10411 | h10411
                                            · rcases p10406_3 (m.d 2 4) (by simp) with h10412 | h10412
                                              · linarith only [h10297, h10412, hlam]
                                              · linarith only [h10306, h10412, hlam]
                                            · linarith only [h10303, h10411, hlam]
                                          · linarith only [h10298, h10410, hlam]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [h10298, h10309, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p10406_1]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [h10295, h10303, h10305, h10309, h8811, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10406_1]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [hlam, p10406_0]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [h10301, h10303, h10308, h10309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10406_1]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          rcases p10406_3 (m.d 0 4) (by simp) with h10421 | h10421
                                          · linarith only [h10421, h8811, hlam]
                                          · linarith only [h10298, h10421, hlam]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [h10301, h10303, h10309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10406_1]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [h10297, hlam, p10406_1]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [h10302, hlam, p10406_1]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [hlam, p10406_0]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [h0, h10297, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10406_1]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [h0, h10296, h10306, h10309, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10406_1]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [h10298, hlam, p10406_1]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [h10303, hlam, p10406_0]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [h10306, hlam, p10406_0]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [hlam, p10406_0]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [h10309, hlam, p10406_0]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [h10300, hlam, p10406_0]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [h10305, hlam, p10406_0]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [h10308, hlam, p10406_0]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [h10295, h10305, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10406_1]
                                        · have p10406_0 := h10406c.1
                                          have p10406_1 := h10406c.2.1
                                          have p10406_2 := h10406c.2.2.1
                                          have p10406_3 := h10406c.2.2.2
                                          linarith only [hlam, p10406_0]
                                  · linarith only [h10401, hlam, p10360_0]
                                · linarith only [h10304, h10400, hlam]
                              · linarith only [h10299, h10399, hlam]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [h10298, hlam, p10360_0]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [h10303, hlam, p10360_0]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [h10306, hlam, p10360_0]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [hlam, p10360_0]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [h10309, hlam, p10360_1]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [h10299, hlam, p10360_0]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [h10304, hlam, p10360_0]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [h10307, hlam, p10360_0]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [h10295, h10301, h10303, h10304, h8811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10360_1]
                            · have p10360_0 := h10360c.1
                              have p10360_1 := h10360c.2.1
                              have p10360_2 := h10360c.2.2.1
                              have p10360_3 := h10360c.2.2.2
                              linarith only [hlam, p10360_0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10453 | h10453
                          · linarith only [h0, h10296, h10306, h10308, h10453, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases h3bigk with h10455c | h10455c | h10455c | h10455c | h10455c | h10455c | h10455c | h10455c | h10455c | h10455c | h10455c | h10455c | h10455c | h10455c | h10455c | h10455c | h10455c | h10455c | h10455c | h10455c | h10455c | h10455c | h10455c | h10455c | h10455c
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              linarith only [hlam, p10455_0]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              linarith only [h7360, hlam, p10455_1]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              rcases p10455_3 (m.d 0 3) (by simp) with h10458 | h10458
                              · rcases p10455_3 (m.d 1 3) (by simp) with h10459 | h10459
                                · rcases p10455_3 (m.d 2 3) (by simp) with h10460 | h10460
                                  · linarith only [h10296, h10460, hlam]
                                  · rcases p10455_3 (m.d 3 4) (by simp) with h10462 | h10462
                                    · linarith only [h10298, h10462, hlam]
                                    · rcases p10455_3 (m.d 3 5) (by simp) with h10464 | h10464
                                      · linarith only [h10299, h10464, hlam]
                                      · rcases h4bigk with h10466c | h10466c | h10466c | h10466c | h10466c | h10466c | h10466c | h10466c | h10466c | h10466c | h10466c | h10466c | h10466c | h10466c | h10466c | h10466c | h10466c | h10466c | h10466c | h10466c | h10466c | h10466c | h10466c | h10466c | h10466c
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [hlam, p10466_0]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [h8811, hlam, p10466_0]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          rcases p10466_3 (m.d 0 4) (by simp) with h10469 | h10469
                                          · rcases p10466_3 (m.d 1 4) (by simp) with h10470 | h10470
                                            · rcases p10466_3 (m.d 2 4) (by simp) with h10471 | h10471
                                              · linarith only [h10297, h10471, hlam]
                                              · rcases p10466_3 (m.d 3 4) (by simp) with h10473 | h10473
                                                · linarith only [h10298, h10473, hlam]
                                                · rcases p10466_3 (m.d 4 5) (by simp) with h10475 | h10475
                                                  · linarith only [h10300, h10475, hlam]
                                                  · linarith only [h10308, h10475, hlam]
                                            · linarith only [h10302, h10470, hlam]
                                          · linarith only [h10297, h10469, hlam]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          rcases p10466_3 (m.d 0 4) (by simp) with h10480 | h10480
                                          · rcases p10466_3 (m.d 1 4) (by simp) with h10481 | h10481
                                            · rcases p10466_3 (m.d 2 4) (by simp) with h10482 | h10482
                                              · linarith only [h10297, h10482, hlam]
                                              · linarith only [h10306, h10482, hlam]
                                            · linarith only [h10303, h10481, hlam]
                                          · linarith only [h10298, h10480, hlam]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [h10306, h10308, hc04, hc34, hlam, hphi, ht0b, ht45, ht5b, p10466_1]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [h10301, h10303, h8811, hc01, hc12, hlam, hphi, p10466_1]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [hlam, p10466_0]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          rcases p10466_3 (m.d 0 4) (by simp) with h10490 | h10490
                                          · linarith only [h10490, h8811, hlam]
                                          · linarith only [h10297, h10490, hlam]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          rcases p10466_3 (m.d 0 4) (by simp) with h10493 | h10493
                                          · linarith only [h10493, h8811, hlam]
                                          · linarith only [h10298, h10493, hlam]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [h10301, h10303, h10306, h10308, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10466_1]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [h10297, hlam, p10466_1]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [h10302, hlam, p10466_1]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [hlam, p10466_0]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [h10295, h10305, h10308, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10466_1]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [h10308, hlam, p10466_0]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [h10298, hlam, p10466_1]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [h10303, hlam, p10466_0]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [h10306, hlam, p10466_0]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [hlam, p10466_0]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [h10453, hlam, p10466_0]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [h10300, hlam, p10466_0]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [h10305, hlam, p10466_0]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [h10295, h10305, h8811, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p10466_1]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [h10295, h10301, h10303, h10305, h8811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10466_1]
                                        · have p10466_0 := h10466c.1
                                          have p10466_1 := h10466c.2.1
                                          have p10466_2 := h10466c.2.2.1
                                          have p10466_3 := h10466c.2.2.2
                                          linarith only [hlam, p10466_0]
                                · linarith only [h10301, h10459, hlam]
                              · linarith only [h10296, h10458, hlam]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              rcases p10455_3 (m.d 0 3) (by simp) with h10514 | h10514
                              · rcases p10455_3 (m.d 1 3) (by simp) with h10515 | h10515
                                · rcases p10455_3 (m.d 2 3) (by simp) with h10516 | h10516
                                  · linarith only [h10296, h10516, hlam]
                                  · linarith only [h10306, h10516, hlam]
                                · linarith only [h10303, h10515, hlam]
                              · linarith only [h10514, hlam, p10455_0]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              rcases p10455_3 (m.d 0 3) (by simp) with h10521 | h10521
                              · rcases p10455_3 (m.d 1 3) (by simp) with h10522 | h10522
                                · rcases p10455_3 (m.d 2 3) (by simp) with h10523 | h10523
                                  · linarith only [h10296, h10523, hlam]
                                  · linarith only [h10307, h10523, hlam]
                                · linarith only [h10304, h10522, hlam]
                              · linarith only [h10521, hlam, p10455_0]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              linarith only [h10295, h10301, h10305, h10308, h7360, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10455_1]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              linarith only [hlam, p10455_0]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              rcases p10455_3 (m.d 0 3) (by simp) with h10530 | h10530
                              · linarith only [h10530, h7360, hlam]
                              · linarith only [h10296, h10530, hlam]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              linarith only [h10295, h10305, h10306, h10308, h7360, hlam, p10455_2]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              rcases p10455_3 (m.d 0 3) (by simp) with h10534 | h10534
                              · linarith only [h10534, h7360, hlam]
                              · linarith only [h10299, h10534, hlam]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              linarith only [h10296, hlam, p10455_0]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              linarith only [h10301, hlam, p10455_0]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              linarith only [hlam, p10455_0]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              rcases p10455_3 (m.d 0 3) (by simp) with h10540 | h10540
                              · rcases p10455_3 (m.d 1 3) (by simp) with h10541 | h10541
                                · rcases p10455_3 (m.d 2 3) (by simp) with h10542 | h10542
                                  · rcases p10455_3 (m.d 3 4) (by simp) with h10543 | h10543
                                    · linarith only [h10543, hlam, p10455_0]
                                    · rcases p10455_3 (m.d 3 5) (by simp) with h10545 | h10545
                                      · linarith only [h10307, h10545, hlam]
                                      · linarith only [h10453, h10545, hlam]
                                  · linarith only [h10542, hlam, p10455_0]
                                · linarith only [h10303, h10541, hlam]
                              · linarith only [h10298, h10540, hlam]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              rcases p10455_3 (m.d 0 3) (by simp) with h10551 | h10551
                              · rcases p10455_3 (m.d 1 3) (by simp) with h10552 | h10552
                                · rcases p10455_3 (m.d 2 3) (by simp) with h10553 | h10553
                                  · rcases p10455_3 (m.d 3 4) (by simp) with h10554 | h10554
                                    · linarith only [h10306, h10554, hlam]
                                    · rcases p10455_3 (m.d 3 5) (by simp) with h10556 | h10556
                                      · linarith only [h10556, hlam, p10455_0]
                                      · rcases h4bigk with h10558c | h10558c | h10558c | h10558c | h10558c | h10558c | h10558c | h10558c | h10558c | h10558c | h10558c | h10558c | h10558c | h10558c | h10558c | h10558c | h10558c | h10558c | h10558c | h10558c | h10558c | h10558c | h10558c | h10558c | h10558c
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [hlam, p10558_0]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [h8811, hlam, p10558_0]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          rcases p10558_3 (m.d 0 4) (by simp) with h10561 | h10561
                                          · rcases p10558_3 (m.d 1 4) (by simp) with h10562 | h10562
                                            · rcases p10558_3 (m.d 2 4) (by simp) with h10563 | h10563
                                              · linarith only [h10297, h10563, hlam]
                                              · rcases p10558_3 (m.d 3 4) (by simp) with h10565 | h10565
                                                · linarith only [h10298, h10565, hlam]
                                                · rcases p10558_3 (m.d 4 5) (by simp) with h10567 | h10567
                                                  · linarith only [h10300, h10567, hlam]
                                                  · linarith only [h10308, h10567, hlam]
                                            · linarith only [h10302, h10562, hlam]
                                          · linarith only [h10297, h10561, hlam]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          rcases p10558_3 (m.d 0 4) (by simp) with h10572 | h10572
                                          · rcases p10558_3 (m.d 1 4) (by simp) with h10573 | h10573
                                            · rcases p10558_3 (m.d 2 4) (by simp) with h10574 | h10574
                                              · linarith only [h10297, h10574, hlam]
                                              · linarith only [h10306, h10574, hlam]
                                            · linarith only [h10303, h10573, hlam]
                                          · linarith only [h10298, h10572, hlam]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [h10298, h10306, h10308, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p10558_1]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [h10295, h10303, h10305, h10306, h10308, h8811, hc13, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10558_1]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [hlam, p10558_0]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          rcases p10558_3 (m.d 0 4) (by simp) with h10582 | h10582
                                          · linarith only [h10582, h8811, hlam]
                                          · linarith only [h10297, h10582, hlam]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          rcases p10558_3 (m.d 0 4) (by simp) with h10585 | h10585
                                          · linarith only [h10585, h8811, hlam]
                                          · linarith only [h10298, h10585, hlam]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [h10301, h10303, h10306, h10308, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10558_1]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [h10297, hlam, p10558_1]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [h10302, hlam, p10558_1]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [hlam, p10558_0]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [h10295, h10305, h10308, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p10558_1]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [h10308, hlam, p10558_0]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [h10298, hlam, p10558_1]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [h10303, hlam, p10558_0]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [h10306, hlam, p10558_0]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [hlam, p10558_0]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [h10453, hlam, p10558_0]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [h10300, hlam, p10558_0]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [h10305, hlam, p10558_0]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [h10295, h10305, h8811, hc04, hc24, hlam, hphi, ht0b, ht45, ht5b, p10558_1]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [h10295, h10301, h10303, h10305, h8811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10558_1]
                                        · have p10558_0 := h10558c.1
                                          have p10558_1 := h10558c.2.1
                                          have p10558_2 := h10558c.2.2.1
                                          have p10558_3 := h10558c.2.2.2
                                          linarith only [hlam, p10558_0]
                                  · linarith only [h10553, hlam, p10455_0]
                                · linarith only [h10304, h10552, hlam]
                              · linarith only [h10299, h10551, hlam]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              linarith only [h10298, hlam, p10455_0]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              linarith only [h10303, hlam, p10455_0]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              linarith only [h10306, hlam, p10455_0]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              linarith only [hlam, p10455_0]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              linarith only [h10453, hlam, p10455_1]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              linarith only [h10299, hlam, p10455_0]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              linarith only [h10304, hlam, p10455_0]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              linarith only [h10307, hlam, p10455_0]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              linarith only [h10295, h10301, h10303, h10304, h8811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p10455_1]
                            · have p10455_0 := h10455c.1
                              have p10455_1 := h10455c.2.1
                              have p10455_2 := h10455c.2.2.1
                              have p10455_3 := h10455c.2.2.2
                              linarith only [hlam, p10455_0]
                      · linarith only [h10295, h10301, h10303, h10304, h10306, h10307, h8811, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10618 | h10618
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10619 | h10619
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10620 | h10620
                          · rcases h3bigk with h10621c | h10621c | h10621c | h10621c | h10621c | h10621c | h10621c | h10621c | h10621c | h10621c | h10621c | h10621c | h10621c | h10621c | h10621c | h10621c | h10621c | h10621c | h10621c | h10621c | h10621c | h10621c | h10621c | h10621c | h10621c
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [hlam, p10621_0]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [h7360, hlam, p10621_1]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              rcases p10621_3 (m.d 0 3) (by simp) with h10624 | h10624
                              · rcases p10621_3 (m.d 1 3) (by simp) with h10625 | h10625
                                · rcases p10621_3 (m.d 2 3) (by simp) with h10626 | h10626
                                  · linarith only [h10296, h10626, hlam]
                                  · rcases p10621_3 (m.d 3 4) (by simp) with h10628 | h10628
                                    · linarith only [h10298, h10628, hlam]
                                    · linarith only [h10306, h10628, hlam]
                                · linarith only [h10301, h10625, hlam]
                              · linarith only [h10296, h10624, hlam]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [h0, h10296, h10306, h10618, h10620, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10621_1]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [h10298, h10306, h10618, hlam, p10621_2]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [h10298, h10301, h10306, h10618, h10620, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10621_1]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [hlam, p10621_0]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              rcases p10621_3 (m.d 0 3) (by simp) with h10637 | h10637
                              · linarith only [h10637, h7360, hlam]
                              · linarith only [h10296, h10637, hlam]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [h10301, h10306, h10618, h10620, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10621_1]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [h10298, h10306, h10618, h7360, hlam, p10621_2]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [h10296, hlam, p10621_0]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [h10301, hlam, p10621_0]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [hlam, p10621_0]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [h10306, hlam, p10621_0]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [h10298, h10306, hc03, hc35, hlam, hphi, ht0b, ht5b, p10621_1]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [h10298, hlam, p10621_0]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [h10303, hlam, p10621_0]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [h10298, h10301, h10618, h7360, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10621_1]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [hlam, p10621_0]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              rcases p10621_3 (m.d 0 3) (by simp) with h10651 | h10651
                              · rcases p10621_3 (m.d 1 3) (by simp) with h10652 | h10652
                                · rcases p10621_3 (m.d 2 3) (by simp) with h10653 | h10653
                                  · linarith only [h10306, h10653, hlam]
                                  · linarith only [h10618, h10653, hlam]
                                · linarith only [h10304, h10652, hlam]
                              · linarith only [h10299, h10651, hlam]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [h10299, hlam, p10621_0]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [h10304, hlam, p10621_0]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [h10618, hlam, p10621_0]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [h10620, hlam, p10621_0]
                            · have p10621_0 := h10621c.1
                              have p10621_1 := h10621c.2.1
                              have p10621_2 := h10621c.2.2.1
                              have p10621_3 := h10621c.2.2.2
                              linarith only [hlam, p10621_0]
                          · linarith only [h10300, h10306, h10618, h10620, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h10295, h10301, h10303, h10305, h10306, h10618, h10619, h8811, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10665 | h10665
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10666 | h10666
                          · rcases h3bigk with h10667c | h10667c | h10667c | h10667c | h10667c | h10667c | h10667c | h10667c | h10667c | h10667c | h10667c | h10667c | h10667c | h10667c | h10667c | h10667c | h10667c | h10667c | h10667c | h10667c | h10667c | h10667c | h10667c | h10667c | h10667c
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              linarith only [hlam, p10667_0]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              linarith only [h7360, hlam, p10667_1]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              rcases p10667_3 (m.d 0 3) (by simp) with h10670 | h10670
                              · rcases p10667_3 (m.d 1 3) (by simp) with h10671 | h10671
                                · rcases p10667_3 (m.d 2 3) (by simp) with h10672 | h10672
                                  · linarith only [h10296, h10672, hlam]
                                  · rcases p10667_3 (m.d 3 4) (by simp) with h10674 | h10674
                                    · linarith only [h10298, h10674, hlam]
                                    · linarith only [h10306, h10674, hlam]
                                · linarith only [h10301, h10671, hlam]
                              · linarith only [h10296, h10670, hlam]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              rcases p10667_3 (m.d 0 3) (by simp) with h10679 | h10679
                              · rcases p10667_3 (m.d 1 3) (by simp) with h10680 | h10680
                                · rcases p10667_3 (m.d 2 3) (by simp) with h10681 | h10681
                                  · linarith only [h10296, h10681, hlam]
                                  · rcases p10667_3 (m.d 3 4) (by simp) with h10683 | h10683
                                    · linarith only [h10683, hlam, p10667_0]
                                    · rcases p10667_3 (m.d 3 5) (by simp) with h10685 | h10685
                                      · linarith only [h10299, h10685, hlam]
                                      · rcases h4bigk with h10687c | h10687c | h10687c | h10687c | h10687c | h10687c | h10687c | h10687c | h10687c | h10687c | h10687c | h10687c | h10687c | h10687c | h10687c | h10687c | h10687c | h10687c | h10687c | h10687c | h10687c | h10687c | h10687c | h10687c | h10687c
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [hlam, p10687_0]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [h8811, hlam, p10687_0]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [h10298, h10665, hc03, hc45, hlam, hphi, ht0b, ht5b, p10687_1]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [h10298, h10301, h10618, h10666, h7360, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10687_1]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          rcases p10687_3 (m.d 0 4) (by simp) with h10692 | h10692
                                          · rcases p10687_3 (m.d 1 4) (by simp) with h10693 | h10693
                                            · rcases p10687_3 (m.d 2 4) (by simp) with h10694 | h10694
                                              · linarith only [h10297, h10694, hlam]
                                              · linarith only [h10665, h10694, hlam]
                                            · linarith only [h10305, h10693, hlam]
                                          · linarith only [h10692, hlam, p10687_0]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [h10301, h10303, h8811, hc01, hc12, hlam, hphi, p10687_1]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [hlam, p10687_0]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [h10301, h10303, h10665, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10687_1]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [h10301, h10303, h10618, h10666, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10687_1]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          rcases p10687_3 (m.d 0 4) (by simp) with h10703 | h10703
                                          · linarith only [h10703, h8811, hlam]
                                          · linarith only [h10300, h10703, hlam]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [h10297, hlam, p10687_1]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [h10302, hlam, p10687_1]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [hlam, p10687_0]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [h10306, hlam, p10687_1]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [h0, h10297, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10687_1]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [h10298, hlam, p10687_1]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [h10303, hlam, p10687_0]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [h10301, h7360, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p10667_1, p10687_1]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [hlam, p10687_0]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [h10301, h7360, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10667_1, p10687_1]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [h10300, hlam, p10687_0]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [h10305, hlam, p10687_0]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [h10665, hlam, p10687_0]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [h10666, hlam, p10687_0]
                                        · have p10687_0 := h10687c.1
                                          have p10687_1 := h10687c.2.1
                                          have p10687_2 := h10687c.2.2.1
                                          have p10687_3 := h10687c.2.2.2
                                          linarith only [hlam, p10687_0]
                                · linarith only [h10303, h10680, hlam]
                              · linarith only [h10679, hlam, p10667_0]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              rcases p10667_3 (m.d 0 3) (by simp) with h10723 | h10723
                              · rcases p10667_3 (m.d 1 3) (by simp) with h10724 | h10724
                                · rcases p10667_3 (m.d 2 3) (by simp) with h10725 | h10725
                                  · linarith only [h10296, h10725, hlam]
                                  · rcases p10667_3 (m.d 3 4) (by simp) with h10727 | h10727
                                    · linarith only [h10298, h10727, hlam]
                                    · linarith only [h10666, h10727, hlam]
                                · linarith only [h10304, h10724, hlam]
                              · linarith only [h10723, hlam, p10667_0]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              linarith only [h10295, h10301, h10304, h10618, h7360, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10667_1]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              linarith only [hlam, p10667_0]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              linarith only [h10295, h10304, h10618, h7360, hlam, p10667_2]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              rcases p10667_3 (m.d 0 3) (by simp) with h10735 | h10735
                              · linarith only [h10735, h7360, hlam]
                              · linarith only [h10298, h10735, hlam]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              rcases p10667_3 (m.d 0 3) (by simp) with h10738 | h10738
                              · linarith only [h10738, h7360, hlam]
                              · linarith only [h10299, h10738, hlam]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              linarith only [h10296, hlam, p10667_0]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              linarith only [h10301, hlam, p10667_0]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              linarith only [hlam, p10667_0]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              linarith only [h10306, hlam, p10667_0]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              linarith only [h10618, hlam, p10667_0]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              linarith only [h10298, hlam, p10667_0]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              linarith only [h10303, hlam, p10667_0]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              rcases p10667_3 (m.d 0 3) (by simp) with h10748 | h10748
                              · rcases p10667_3 (m.d 1 3) (by simp) with h10749 | h10749
                                · rcases p10667_3 (m.d 2 3) (by simp) with h10750 | h10750
                                  · linarith only [h10750, hlam, p10667_0]
                                  · rcases p10667_3 (m.d 3 4) (by simp) with h10752 | h10752
                                    · rcases p10667_3 (m.d 3 5) (by simp) with h10753 | h10753
                                      · linarith only [h10666, h10753, hlam]
                                      · linarith only [h10618, h10753, hlam]
                                    · linarith only [h10752, hlam, p10667_0]
                                · linarith only [h10301, h10749, hlam]
                              · linarith only [h10296, h10748, hlam]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              linarith only [hlam, p10667_0]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              linarith only [h10298, h10618, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10667_1]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              linarith only [h10299, hlam, p10667_0]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              linarith only [h10304, hlam, p10667_0]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              linarith only [h10295, h10303, h10304, h8811, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10667_1]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              linarith only [h10666, hlam, p10667_0]
                            · have p10667_0 := h10667c.1
                              have p10667_1 := h10667c.2.1
                              have p10667_2 := h10667c.2.2.1
                              have p10667_3 := h10667c.2.2.2
                              linarith only [hlam, p10667_0]
                          · linarith only [h0, h10297, h10306, h10665, h10666, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10767 | h10767
                          · rcases h3bigk with h10768c | h10768c | h10768c | h10768c | h10768c | h10768c | h10768c | h10768c | h10768c | h10768c | h10768c | h10768c | h10768c | h10768c | h10768c | h10768c | h10768c | h10768c | h10768c | h10768c | h10768c | h10768c | h10768c | h10768c | h10768c
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [hlam, p10768_0]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [h7360, hlam, p10768_1]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [h10298, h10306, h10665, h10767, hlam, p10768_2]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [h10306, h10665, h10767, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10768_1]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              rcases p10768_3 (m.d 0 3) (by simp) with h10773 | h10773
                              · rcases p10768_3 (m.d 1 3) (by simp) with h10774 | h10774
                                · rcases p10768_3 (m.d 2 3) (by simp) with h10775 | h10775
                                  · linarith only [h10296, h10775, hlam]
                                  · rcases p10768_3 (m.d 3 4) (by simp) with h10777 | h10777
                                    · linarith only [h10298, h10777, hlam]
                                    · linarith only [h10767, h10777, hlam]
                                · linarith only [h10304, h10774, hlam]
                              · linarith only [h10773, hlam, p10768_0]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [h10295, h10301, h10304, h10306, h10665, h10767, h7360, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10768_1]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [hlam, p10768_0]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [h10295, h10304, h10306, h10665, h10767, h7360, hlam, p10768_2]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [h10306, h10665, h10767, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10768_1]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              rcases p10768_3 (m.d 0 3) (by simp) with h10786 | h10786
                              · linarith only [h10786, h7360, hlam]
                              · linarith only [h10299, h10786, hlam]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [h10296, hlam, p10768_0]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [h10301, hlam, p10768_0]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [hlam, p10768_0]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [h10306, hlam, p10768_0]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [h10618, hlam, p10768_0]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [h10298, hlam, p10768_0]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [h10303, hlam, p10768_0]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              rcases p10768_3 (m.d 0 3) (by simp) with h10796 | h10796
                              · rcases p10768_3 (m.d 1 3) (by simp) with h10797 | h10797
                                · rcases p10768_3 (m.d 2 3) (by simp) with h10798 | h10798
                                  · linarith only [h10798, hlam, p10768_0]
                                  · rcases p10768_3 (m.d 3 4) (by simp) with h10800 | h10800
                                    · rcases p10768_3 (m.d 3 5) (by simp) with h10801 | h10801
                                      · linarith only [h10767, h10801, hlam]
                                      · linarith only [h10618, h10801, hlam]
                                    · linarith only [h10800, hlam, p10768_0]
                                · linarith only [h10301, h10797, hlam]
                              · linarith only [h10296, h10796, hlam]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [hlam, p10768_0]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [h10298, h10306, h10665, h10767, hc03, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p10768_1]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [h10299, hlam, p10768_0]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [h10304, hlam, p10768_0]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [h10295, h10304, h8811, hc14, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10768_1]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [h10767, hlam, p10768_0]
                            · have p10768_0 := h10768c.1
                              have p10768_1 := h10768c.2.1
                              have p10768_2 := h10768c.2.2.1
                              have p10768_3 := h10768c.2.2.2
                              linarith only [hlam, p10768_0]
                          · linarith only [h10295, h10301, h10303, h10305, h10306, h10767, h8811, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h10300, h10305, h8811, hlam]
                · linarith only [h10299, h10304, h7360, hlam]
              · linarith only [h10298, h10303, h7360, hlam]
            · linarith only [h0, h10297, h10302, hlam]
          · linarith only [h0, h10295, h10296, h10301, hc02, hc15, hlam, hphi, ht0b, ht5b]
        · linarith only [h10295, h10300, h8811, hlam]
      · linarith only [h10295, h10298, h10299, h8811, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h10822 | h10822
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10823 | h10823
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10824 | h10824
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10825 | h10825
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10826 | h10826
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10827 | h10827
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10828 | h10828
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10829 | h10829
                    · linarith only [h10296, h10298, h10829, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10831 | h10831
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10832 | h10832
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10833 | h10833
                          · rcases h3bigk with h10834c | h10834c | h10834c | h10834c | h10834c | h10834c | h10834c | h10834c | h10834c | h10834c | h10834c | h10834c | h10834c | h10834c | h10834c | h10834c | h10834c | h10834c | h10834c | h10834c | h10834c | h10834c | h10834c | h10834c | h10834c
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [hlam, p10834_0]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [h7360, hlam, p10834_1]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [h10298, h10824, h10826, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p10834_1]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [h10298, hlam, p10834_0]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [h10298, h10824, h10826, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p10834_1]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              rcases p10834_3 (m.d 0 3) (by simp) with h10840 | h10840
                              · linarith only [h10840, h7360, hlam]
                              · rcases p10834_3 (m.d 1 3) (by simp) with h10842 | h10842
                                · rcases p10834_3 (m.d 2 3) (by simp) with h10843 | h10843
                                  · linarith only [h10824, h10843, hlam]
                                  · rcases p10834_3 (m.d 3 4) (by simp) with h10845 | h10845
                                    · linarith only [h10826, h10845, hlam]
                                    · linarith only [h10298, h10845, hlam]
                                · linarith only [h10842, h7360, hlam]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [hlam, p10834_0]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              rcases p10834_3 (m.d 0 3) (by simp) with h10850 | h10850
                              · linarith only [h10850, h7360, hlam]
                              · linarith only [h10296, h10850, hlam]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [h10298, h10824, h7360, hc01, hc12, hlam, hphi, p10834_1]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [h10296, h10298, h10826, h10831, hlam, p10834_2]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [h10296, hlam, p10834_0]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [h10824, hlam, p10834_0]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [hlam, p10834_0]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [h10829, hlam, p10834_0]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [h10296, h10298, h10826, h10833, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p10834_1]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [h10295, h10826, h7360, hc13, hc15, hlam, hphi, ht01, ht0b, ht5b, p10834_1]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [h10826, hlam, p10834_0]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [h10824, h10826, h10831, h10833, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10834_1]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [hlam, p10834_0]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              rcases p10834_3 (m.d 0 3) (by simp) with h10864 | h10864
                              · linarith only [h10298, h10864, hlam]
                              · linarith only [h10822, h10864, hlam]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [h10822, hlam, p10834_0]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [h10827, hlam, p10834_0]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [h10831, hlam, p10834_0]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [h10833, hlam, p10834_0]
                            · have p10834_0 := h10834c.1
                              have p10834_1 := h10834c.2.1
                              have p10834_2 := h10834c.2.2.1
                              have p10834_3 := h10834c.2.2.2
                              linarith only [hlam, p10834_0]
                          · linarith only [h10295, h10298, h10823, h10827, h10833, h7360, hc04, hc35, hlam, hphi, ht0b, ht5b]
                        · linarith only [h10295, h10298, h10826, h10828, h10829, h10831, h10832, h7360, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h10298, h10822, h10824, h10826, h10831, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h10823, h10828, h8811, hlam]
                · linarith only [h10298, h10826, h10827, h7360, hc01, hc35, hlam, hphi, ht12, ht23]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10877 | h10877
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10878 | h10878
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10879 | h10879
                    · linarith only [h10295, h10826, h10877, h10879, h7360, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10881 | h10881
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h10882 | h10882
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h10883 | h10883
                          · rcases h3bigk with h10884c | h10884c | h10884c | h10884c | h10884c | h10884c | h10884c | h10884c | h10884c | h10884c | h10884c | h10884c | h10884c | h10884c | h10884c | h10884c | h10884c | h10884c | h10884c | h10884c | h10884c | h10884c | h10884c | h10884c | h10884c
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [hlam, p10884_0]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [h7360, hlam, p10884_1]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [h10298, h10881, h10883, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10884_1]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [h10298, hlam, p10884_0]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              rcases p10884_3 (m.d 0 3) (by simp) with h10889 | h10889
                              · rcases p10884_3 (m.d 1 3) (by simp) with h10890 | h10890
                                · rcases p10884_3 (m.d 2 3) (by simp) with h10891 | h10891
                                  · linarith only [h10296, h10891, hlam]
                                  · linarith only [h10881, h10891, hlam]
                                · linarith only [h10877, h10890, hlam]
                              · linarith only [h10889, hlam, p10884_0]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [h10826, hc03, hc34, hlam, hphi, p10884_1]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [hlam, p10884_0]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [h10826, h10881, h10883, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10884_1]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [h10826, hlam, p10884_0]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              rcases p10884_3 (m.d 0 3) (by simp) with h10900 | h10900
                              · linarith only [h10900, h7360, hlam]
                              · linarith only [h10822, h10900, hlam]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [h10296, hlam, p10884_0]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [h10824, hlam, p10884_0]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [hlam, p10884_0]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [h10879, hlam, p10884_0]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              rcases p10884_3 (m.d 0 3) (by simp) with h10907 | h10907
                              · rcases p10884_3 (m.d 1 3) (by simp) with h10908 | h10908
                                · rcases p10884_3 (m.d 2 3) (by simp) with h10909 | h10909
                                  · rcases p10884_3 (m.d 3 4) (by simp) with h10910 | h10910
                                    · rcases p10884_3 (m.d 3 5) (by simp) with h10911 | h10911
                                      · linarith only [h10911, hlam, p10884_0]
                                      · rcases h4bigk with h10913c | h10913c | h10913c | h10913c | h10913c | h10913c | h10913c | h10913c | h10913c | h10913c | h10913c | h10913c | h10913c | h10913c | h10913c | h10913c | h10913c | h10913c | h10913c | h10913c | h10913c | h10913c | h10913c | h10913c | h10913c
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [hlam, p10913_0]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [h8811, hlam, p10913_0]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [h10826, h10879, h10883, h8811, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10884_1, p10913_1]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [h10298, hlam, p10913_0]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          rcases p10913_3 (m.d 0 4) (by simp) with h10918 | h10918
                                          · rcases p10913_3 (m.d 1 4) (by simp) with h10919 | h10919
                                            · rcases p10913_3 (m.d 2 4) (by simp) with h10920 | h10920
                                              · linarith only [h10297, h10920, hlam]
                                              · linarith only [h10882, h10920, hlam]
                                            · linarith only [h10878, h10919, hlam]
                                          · linarith only [h10918, hlam, p10913_0]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [h10295, h10826, h10877, h10883, h8811, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10913_1]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [hlam, p10913_0]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [h10826, h10879, h10883, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10884_1, p10913_1]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [h10826, hlam, p10913_1]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          rcases p10913_3 (m.d 0 4) (by simp) with h10929 | h10929
                                          · linarith only [h10929, h8811, hlam]
                                          · linarith only [h10823, h10929, hlam]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [h10297, hlam, p10913_1]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [h10825, hlam, p10913_1]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [hlam, p10913_0]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [h10879, hlam, p10913_1]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [h0, h10297, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p10913_1]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [h10295, h10877, h10883, h8811, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10913_1]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [h10295, h10877, h10883, h8811, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10913_1]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [h10879, h10883, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10884_1, p10913_1]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [hlam, p10913_0]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          rcases p10913_3 (m.d 0 4) (by simp) with h10941 | h10941
                                          · linarith only [h10298, h10941, hlam]
                                          · linarith only [h10823, h10941, hlam]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [h10823, hlam, p10913_0]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [h10878, hlam, p10913_0]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [h10882, hlam, p10913_0]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [h10883, hlam, p10913_0]
                                        · have p10913_0 := h10913c.1
                                          have p10913_1 := h10913c.2.1
                                          have p10913_2 := h10913c.2.2.1
                                          have p10913_3 := h10913c.2.2.2
                                          linarith only [hlam, p10913_0]
                                    · linarith only [h10883, h10910, hlam]
                                  · linarith only [h10909, hlam, p10884_0]
                                · linarith only [h10877, h10908, hlam]
                              · linarith only [h10822, h10907, hlam]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              rcases p10884_3 (m.d 0 3) (by simp) with h10953 | h10953
                              · linarith only [h10953, hlam, p10884_0]
                              · rcases p10884_3 (m.d 1 3) (by simp) with h10955 | h10955
                                · linarith only [h10826, h10955, hlam]
                                · linarith only [h10955, h7360, hlam]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [h10295, h10877, h10883, h7360, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p10884_1]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              rcases p10884_3 (m.d 0 3) (by simp) with h10959 | h10959
                              · linarith only [h10298, h10959, hlam]
                              · linarith only [h10296, h10959, hlam]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [hlam, p10884_0]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [h10295, h10826, h10877, h7360, hlam, p10884_2]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [h10822, hlam, p10884_0]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [h10877, hlam, p10884_0]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [h10881, hlam, p10884_0]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [h10883, hlam, p10884_0]
                            · have p10884_0 := h10884c.1
                              have p10884_1 := h10884c.2.1
                              have p10884_2 := h10884c.2.2.1
                              have p10884_3 := h10884c.2.2.2
                              linarith only [hlam, p10884_0]
                          · linarith only [h10295, h10826, h10877, h10883, h7360, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                        · linarith only [h10295, h10826, h10878, h10879, h10882, h7360, hc23, hc34, hlam, hphi]
                      · linarith only [h10295, h10826, h10877, h10881, h7360, hc23, hc34, hlam, hphi]
                  · linarith only [h10295, h10823, h10826, h10877, h10878, h7360, hc04, hc35, hlam, hphi, ht0b, ht5b]
                · linarith only [h10295, h10822, h10877, h7360, hc03, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h10297, h10825, hlam]
          · linarith only [h0, h10296, h10824, hlam]
        · linarith only [h10295, h10298, h10823, h7360, hlam]
      · linarith only [h10295, h10822, h7360, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h10978 | h10978
    · linarith only [h10296, h10297, h10978, hlam]
    · rcases m.htr 0 3 5 (by decide) (by decide) with h10980 | h10980
      · rcases m.htr 0 4 5 (by decide) (by decide) with h10981 | h10981
        · rcases m.htr 1 2 3 (by decide) (by decide) with h10982 | h10982
          · rcases m.htr 1 2 4 (by decide) (by decide) with h10983 | h10983
            · rcases m.htr 1 3 4 (by decide) (by decide) with h10984 | h10984
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10985 | h10985
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10986 | h10986
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10987 | h10987
                    · linarith only [h10295, h10296, h10978, h10985, h10987, h7360, hc02, hc35, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10989 | h10989
                      · linarith only [h10296, h10297, h10982, h10984, h10987, h10989, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h10295, h10297, h10982, h10984, h10985, h10987, h10989, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h10981, h10986, h8811, hlam]
                · linarith only [h10296, h10297, h10980, h10983, h10985, h7360, hc01, hc14, hlam, hphi]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h10994 | h10994
                · rcases m.htr 1 4 5 (by decide) (by decide) with h10995 | h10995
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10996 | h10996
                    · linarith only [h10296, h10297, h10983, h10984, h10996, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h10998 | h10998
                      · linarith only [h10296, h10297, h10983, h10998, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h10295, h10984, h10994, h10998, h7360, hc23, hc34, hlam, hphi]
                  · linarith only [h10296, h10297, h10983, h10995, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h10295, h10980, h10994, h7360, hc03, hc15, hlam, hphi, ht0b, ht5b]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h11003 | h11003
              · linarith only [h10978, h10980, h10982, h10983, h11003, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h11005 | h11005
                · rcases m.htr 1 4 5 (by decide) (by decide) with h11006 | h11006
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h11007 | h11007
                    · linarith only [h10295, h11003, h11005, h11007, h7360, hc23, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h11009 | h11009
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h11010 | h11010
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h11011 | h11011
                          · rcases h3bigk with h11012c | h11012c | h11012c | h11012c | h11012c | h11012c | h11012c | h11012c | h11012c | h11012c | h11012c | h11012c | h11012c | h11012c | h11012c | h11012c | h11012c | h11012c | h11012c | h11012c | h11012c | h11012c | h11012c | h11012c | h11012c
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [hlam, p11012_0]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [h7360, hlam, p11012_1]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [h10982, h10983, h11007, h7360, hc23, hc34, hlam, hphi, p11012_1]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [h10978, hlam, p11012_0]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              rcases p11012_3 (m.d 0 3) (by simp) with h11017 | h11017
                              · rcases p11012_3 (m.d 1 3) (by simp) with h11018 | h11018
                                · rcases p11012_3 (m.d 2 3) (by simp) with h11019 | h11019
                                  · linarith only [h10296, h11019, hlam]
                                  · linarith only [h11009, h11019, hlam]
                                · linarith only [h11005, h11018, hlam]
                              · linarith only [h11017, hlam, p11012_0]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [h10982, h10983, h11007, hc03, hc34, hlam, hphi, p11012_1]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [hlam, p11012_0]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [h10982, h10983, h11007, h11009, h11011, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11012_1]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [h11003, hlam, p11012_0]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              rcases p11012_3 (m.d 0 3) (by simp) with h11028 | h11028
                              · linarith only [h11028, h7360, hlam]
                              · linarith only [h10980, h11028, hlam]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [h10296, hlam, p11012_0]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [h10982, hlam, p11012_0]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [hlam, p11012_0]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [h11007, hlam, p11012_0]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [h0, h10296, h10983, h11007, h11011, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11012_1]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              rcases p11012_3 (m.d 0 3) (by simp) with h11036 | h11036
                              · linarith only [h11036, hlam, p11012_0]
                              · rcases p11012_3 (m.d 1 3) (by simp) with h11038 | h11038
                                · linarith only [h11003, h11038, hlam]
                                · linarith only [h11038, h7360, hlam]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [h10295, h11005, h11011, h7360, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p11012_1]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              rcases p11012_3 (m.d 0 3) (by simp) with h11042 | h11042
                              · linarith only [h10978, h11042, hlam]
                              · linarith only [h10296, h11042, hlam]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [hlam, p11012_0]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [h0, h10295, h10983, h11005, h11007, hlam, p11012_2]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [h10980, hlam, p11012_0]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [h11005, hlam, p11012_0]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [h11009, hlam, p11012_0]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [h11011, hlam, p11012_0]
                            · have p11012_0 := h11012c.1
                              have p11012_1 := h11012c.2.1
                              have p11012_2 := h11012c.2.2.1
                              have p11012_3 := h11012c.2.2.2
                              linarith only [hlam, p11012_0]
                          · linarith only [h10295, h10982, h10983, h11005, h11007, h11011, h7360, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                        · linarith only [h10295, h10982, h10983, h11006, h11010, h7360, hlam]
                      · linarith only [h10295, h10982, h10983, h11005, h11009, h7360, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h10981, h11006, h8811, hlam]
                · linarith only [h10295, h10980, h11005, h7360, hc03, hc15, hlam, hphi, ht0b, ht5b]
          · linarith only [h0, h10296, h10982, hlam]
        · linarith only [h0, h10295, h10297, h10981, hlam]
      · linarith only [h10295, h10980, h7360, hlam]

end R2N4
