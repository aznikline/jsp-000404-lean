import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8080000 in
set_option maxHeartbeats 8080000 in
theorem r1l7_11_23_L_I_H_I_s14_x1_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (hg11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (hg12794 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
    (hg13812 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
    (h14856 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h17362 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h11385 := hg11385
  have h12794 := hg12794
  have h13812 := hg13812
  rcases m.htr 0 3 4 (by decide) (by decide) with h17363 | h17363
  · rcases m.htr 0 3 5 (by decide) (by decide) with h17364 | h17364
    · rcases m.htr 0 4 5 (by decide) (by decide) with h17365 | h17365
      · rcases m.htr 1 2 3 (by decide) (by decide) with h17366 | h17366
        · rcases m.htr 1 2 4 (by decide) (by decide) with h17367 | h17367
          · rcases m.htr 1 2 5 (by decide) (by decide) with h17368 | h17368
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17369 | h17369
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17370 | h17370
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17371 | h17371
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17372 | h17372
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17373 | h17373
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h17374 | h17374
                        · linarith only [h14856, h17362, h17366, h17374, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b]
                        · linarith only [h14856, h17362, h17365, h17366, h17374, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h14856, h17362, h17364, h17365, h17373, hlam]
                    · linarith only [h14856, h17363, h17372, hlam]
                  · linarith only [h12794, h14856, h17362, h17365, h17366, h17371, hc01, hc13, hlam, hphi]
                · linarith only [h14856, h17362, h17364, h17365, h17366, h17370, hc03, hc45, hlam, hphi, ht0b, ht5b]
              · linarith only [h11385, h14856, h17362, h17363, h17366, h17369, hc01, hc12, hlam, hphi]
            · linarith only [h14856, h17366, h17368, hc02, hc25, hlam, hphi]
          · linarith only [h14856, h17362, h17366, h17367, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h17384 | h17384
          · rcases m.htr 1 2 5 (by decide) (by decide) with h17385 | h17385
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17386 | h17386
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17387 | h17387
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17388 | h17388
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17389 | h17389
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17390 | h17390
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h17391 | h17391
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h17392 | h17392
                          · rcases h1bigk with h17393c | h17393c | h17393c | h17393c | h17393c | h17393c | h17393c | h17393c | h17393c | h17393c | h17393c | h17393c | h17393c | h17393c | h17393c | h17393c | h17393c | h17393c | h17393c | h17393c | h17393c | h17393c | h17393c | h17393c | h17393c
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [hlam, p17393_0]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [h0, hlam, p17393_0]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [h11385, hlam, p17393_0]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [h12794, hlam, p17393_0]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [h13812, hlam, p17393_0]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [h17366, hc01, hc23, hlam, hphi, ht12, p17393_1]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [hlam, p17393_0]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [h17366, hlam, p17393_0]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [h12794, h17366, hc01, hc23, hlam, hphi, ht12, p17393_1]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [h13812, h17366, hc01, hc23, hlam, hphi, ht12, p17393_1]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              rcases p17393_3 (m.d 0 1) (by simp) with h17404 | h17404
                              · linarith only [h17404, hlam, p17393_0]
                              · rcases p17393_3 (m.d 1 2) (by simp) with h17406 | h17406
                                · linarith only [h17366, h17406, hlam]
                                · linarith only [h0, h17406, hlam]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [h0, h17366, hc01, hc23, hlam, hphi, ht12, p17393_1]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [hlam, p17393_0]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [h13812, h17366, h17388, hc01, hc23, hlam, hphi, ht12, p17393_1]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [h13812, h17366, hc01, hc23, hlam, hphi, ht12, p17393_1]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [h17366, h17384, hc01, hc23, hlam, hphi, ht12, p17393_1]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [h17384, hlam, p17393_1]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [h17386, hlam, p17393_0]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [hlam, p17393_0]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [h13812, h17366, h17384, hc01, hc23, hlam, hphi, ht12, p17393_1]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [h17366, h17385, hc01, hc23, hlam, hphi, ht12, p17393_1]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [h17385, hlam, p17393_1]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [h17387, hlam, p17393_0]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [h17388, hlam, p17393_0]
                            · have p17393_0 := h17393c.1
                              have p17393_1 := h17393c.2.1
                              have p17393_2 := h17393c.2.2.1
                              have p17393_3 := h17393c.2.2.2
                              linarith only [hlam, p17393_0]
                          · linarith only [h0, h17362, h17366, h17391, h17392, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h17424 | h17424
                          · linarith only [h17389, h17391, h17424, hlam]
                          · rcases h1bigk with h17426c | h17426c | h17426c | h17426c | h17426c | h17426c | h17426c | h17426c | h17426c | h17426c | h17426c | h17426c | h17426c | h17426c | h17426c | h17426c | h17426c | h17426c | h17426c | h17426c | h17426c | h17426c | h17426c | h17426c | h17426c
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [hlam, p17426_0]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [h0, hlam, p17426_0]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [h11385, hlam, p17426_0]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [h12794, hlam, p17426_0]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [h13812, hlam, p17426_0]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [h17366, hc01, hc23, hlam, hphi, ht12, p17426_1]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [hlam, p17426_0]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [h17366, hlam, p17426_0]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [h12794, h17366, hc01, hc23, hlam, hphi, ht12, p17426_1]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [h13812, h17366, hc01, hc23, hlam, hphi, ht12, p17426_1]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              rcases p17426_3 (m.d 0 1) (by simp) with h17437 | h17437
                              · linarith only [h17437, hlam, p17426_0]
                              · rcases p17426_3 (m.d 1 2) (by simp) with h17439 | h17439
                                · linarith only [h17366, h17439, hlam]
                                · linarith only [h0, h17439, hlam]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [h0, h17362, h17365, h17366, h17391, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17426_1]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [hlam, p17426_0]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [h12794, h17365, h17366, h17389, h17391, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17426_1]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [h13812, h17366, hc01, hc23, hlam, hphi, ht12, p17426_1]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [h17366, h17384, hc01, hc23, hlam, hphi, ht12, p17426_1]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [h17384, hlam, p17426_1]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [h17386, hlam, p17426_0]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [hlam, p17426_0]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [h13812, h17366, h17384, hc01, hc23, hlam, hphi, ht12, p17426_1]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [h17366, h17385, hc01, hc23, hlam, hphi, ht12, p17426_1]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [h17385, hlam, p17426_1]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [h17387, hlam, p17426_0]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [h17388, hlam, p17426_0]
                            · have p17426_0 := h17426c.1
                              have p17426_1 := h17426c.2.1
                              have p17426_2 := h17426c.2.2.1
                              have p17426_3 := h17426c.2.2.2
                              linarith only [hlam, p17426_0]
                      · linarith only [h17364, h17366, h17385, h17390, hc03, hc25, hlam, hphi, ht0b, ht5b]
                    · linarith only [h0, h17366, h17389, hc01, hc34, hlam, hphi, ht12, ht23]
                  · linarith only [h0, h12794, h17362, h17365, h17388, hc01, hc12, hlam, hphi]
                · linarith only [h0, h11385, h17362, h17364, h17365, h17366, h17387, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h11385, h17363, h17386, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17461 | h17461
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17462 | h17462
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17463 | h17463
                  · linarith only [h17384, h17385, h17463, hlam]
                  · linarith only [h0, h12794, h17362, h17365, h17366, h17463, hc01, hc23, hlam, hphi, ht12]
                · linarith only [h11385, h17364, h17462, hlam]
              · linarith only [h11385, h17363, h17461, hlam]
          · linarith only [h0, h17362, h17384, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h17469 | h17469
        · rcases m.htr 1 2 4 (by decide) (by decide) with h17470 | h17470
          · rcases m.htr 1 2 5 (by decide) (by decide) with h17471 | h17471
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17472 | h17472
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17473 | h17473
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17474 | h17474
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17475 | h17475
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17476 | h17476
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h17477 | h17477
                        · linarith only [h11385, h12794, h14856, h17362, h17365, h17477, hc01, hc13, hlam, hphi]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h17479 | h17479
                          · linarith only [h12794, h14856, h17362, h17365, h17469, h17475, h17479, hc01, hc12, hlam, hphi]
                          · rcases h1bigk with h17481c | h17481c | h17481c | h17481c | h17481c | h17481c | h17481c | h17481c | h17481c | h17481c | h17481c | h17481c | h17481c | h17481c | h17481c | h17481c | h17481c | h17481c | h17481c | h17481c | h17481c | h17481c | h17481c | h17481c | h17481c
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [hlam, p17481_0]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [h0, hlam, p17481_0]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [h11385, hlam, p17481_0]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [h12794, hlam, p17481_0]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [h13812, hlam, p17481_0]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              rcases p17481_3 (m.d 0 1) (by simp) with h17487 | h17487
                              · linarith only [h17487, hlam, p17481_0]
                              · rcases p17481_3 (m.d 1 2) (by simp) with h17489 | h17489
                                · rcases p17481_3 (m.d 1 3) (by simp) with h17490 | h17490
                                  · linarith only [h17469, h17490, hlam]
                                  · linarith only [h11385, h17490, hlam]
                                · linarith only [h17489, hlam, p17481_0]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [hlam, p17481_0]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [h11385, hc01, hc12, hlam, hphi, p17481_1]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [h12794, h17365, h17474, hc01, hc12, hlam, hphi, p17481_1]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [h12794, h17365, h17474, hc01, hc12, hlam, hphi, p17481_1]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              rcases p17481_3 (m.d 0 1) (by simp) with h17498 | h17498
                              · linarith only [h17498, hlam, p17481_0]
                              · rcases p17481_3 (m.d 1 2) (by simp) with h17500 | h17500
                                · rcases p17481_3 (m.d 1 3) (by simp) with h17501 | h17501
                                  · rcases p17481_3 (m.d 1 4) (by simp) with h17502 | h17502
                                    · linarith only [h17472, h17502, hlam]
                                    · linarith only [h12794, h17502, hlam]
                                  · linarith only [h17501, hlam, p17481_0]
                                · linarith only [h0, h17500, hlam]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [h17469, hlam, p17481_1]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [hlam, p17481_0]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [h12794, h17365, h17474, hc01, hc13, hlam, hphi, p17481_1]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [h12794, h17365, h17469, h17474, hc01, hc12, hlam, hphi, p17481_1]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              rcases p17481_3 (m.d 0 1) (by simp) with h17511 | h17511
                              · linarith only [h17511, hlam, p17481_0]
                              · rcases p17481_3 (m.d 1 2) (by simp) with h17513 | h17513
                                · rcases p17481_3 (m.d 1 3) (by simp) with h17514 | h17514
                                  · rcases p17481_3 (m.d 1 4) (by simp) with h17515 | h17515
                                    · rcases p17481_3 (m.d 1 5) (by simp) with h17516 | h17516
                                      · linarith only [h17474, h17516, hlam]
                                      · linarith only [h13812, h17516, hlam]
                                    · linarith only [h17515, hlam, p17481_0]
                                  · linarith only [h11385, h17514, hlam]
                                · linarith only [h0, h17513, hlam]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [h17470, hlam, p17481_1]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [h17472, hlam, p17481_0]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [hlam, p17481_0]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [h12794, h17365, h17474, hc01, hc14, hlam, hphi, p17481_1]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              rcases p17481_3 (m.d 0 1) (by simp) with h17526 | h17526
                              · linarith only [h17526, hlam, p17481_0]
                              · rcases p17481_3 (m.d 1 2) (by simp) with h17528 | h17528
                                · rcases p17481_3 (m.d 1 3) (by simp) with h17529 | h17529
                                  · rcases p17481_3 (m.d 1 4) (by simp) with h17530 | h17530
                                    · rcases p17481_3 (m.d 1 5) (by simp) with h17531 | h17531
                                      · rcases h3bigk with h17532c | h17532c | h17532c | h17532c | h17532c | h17532c | h17532c | h17532c | h17532c | h17532c | h17532c | h17532c | h17532c | h17532c | h17532c | h17532c | h17532c | h17532c | h17532c | h17532c | h17532c | h17532c | h17532c | h17532c | h17532c
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [hlam, p17532_0]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [h11385, hlam, p17532_1]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [h14856, hlam, p17532_1]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [h14856, h17469, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17532_1]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [h14856, h17469, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p17532_1]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [h11385, h17469, hc01, hc12, hlam, hphi, p17532_1]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [hlam, p17532_0]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [h14856, h17469, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p17532_1]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          rcases p17532_3 (m.d 0 3) (by simp) with h17541 | h17541
                                          · linarith only [h11385, h17541, hlam]
                                          · linarith only [h17363, h17541, hlam]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          rcases p17532_3 (m.d 0 3) (by simp) with h17544 | h17544
                                          · linarith only [h11385, h17544, hlam]
                                          · linarith only [h17364, h17544, hlam]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [h14856, h17362, h17475, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17532_1]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [h17469, hlam, p17532_0]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [hlam, p17532_0]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [h17469, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17532_1]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [h17469, h17479, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p17532_1]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [h17363, hlam, p17532_0]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [h17472, hlam, p17532_0]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [h17475, hlam, p17532_0]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [hlam, p17532_0]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [h17479, hlam, p17532_1]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [h17364, hlam, p17532_0]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [h17473, hlam, p17532_0]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [h17476, hlam, p17532_0]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [h17364, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p17532_1]
                                        · have p17532_0 := h17532c.1
                                          have p17532_1 := h17532c.2.1
                                          have p17532_2 := h17532c.2.2.1
                                          have p17532_3 := h17532c.2.2.2
                                          linarith only [hlam, p17532_0]
                                      · linarith only [h17531, hlam, p17481_0]
                                    · linarith only [h12794, h17530, hlam]
                                  · linarith only [h11385, h17529, hlam]
                                · linarith only [h0, h17528, hlam]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [h17471, hlam, p17481_1]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [h17473, hlam, p17481_0]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [h17474, hlam, p17481_0]
                            · have p17481_0 := h17481c.1
                              have p17481_1 := h17481c.2.1
                              have p17481_2 := h17481c.2.2.1
                              have p17481_3 := h17481c.2.2.2
                              linarith only [hlam, p17481_0]
                      · linarith only [h14856, h17364, h17476, hlam]
                    · linarith only [h14856, h17363, h17475, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17572 | h17572
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17573 | h17573
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h17574 | h17574
                        · linarith only [h17362, h17365, h17574, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h17576 | h17576
                          · linarith only [h14856, h17362, h17469, h17474, h17572, h17576, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases h1bigk with h17578c | h17578c | h17578c | h17578c | h17578c | h17578c | h17578c | h17578c | h17578c | h17578c | h17578c | h17578c | h17578c | h17578c | h17578c | h17578c | h17578c | h17578c | h17578c | h17578c | h17578c | h17578c | h17578c | h17578c | h17578c
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [hlam, p17578_0]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [h0, hlam, p17578_0]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [h11385, hlam, p17578_0]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [h12794, hlam, p17578_0]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [h13812, hlam, p17578_0]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              rcases p17578_3 (m.d 0 1) (by simp) with h17584 | h17584
                              · linarith only [h17584, hlam, p17578_0]
                              · rcases p17578_3 (m.d 1 2) (by simp) with h17586 | h17586
                                · rcases p17578_3 (m.d 1 3) (by simp) with h17587 | h17587
                                  · linarith only [h17469, h17587, hlam]
                                  · linarith only [h11385, h17587, hlam]
                                · linarith only [h17586, hlam, p17578_0]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [hlam, p17578_0]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [h11385, hc01, hc12, hlam, hphi, p17578_1]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [h12794, hc01, hc12, hlam, hphi, p17578_1]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [h13812, hc01, hc12, hlam, hphi, p17578_1]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              rcases p17578_3 (m.d 0 1) (by simp) with h17595 | h17595
                              · linarith only [h17595, hlam, p17578_0]
                              · rcases p17578_3 (m.d 1 2) (by simp) with h17597 | h17597
                                · rcases p17578_3 (m.d 1 3) (by simp) with h17598 | h17598
                                  · rcases p17578_3 (m.d 1 4) (by simp) with h17599 | h17599
                                    · linarith only [h17472, h17599, hlam]
                                    · linarith only [h12794, h17599, hlam]
                                  · linarith only [h17598, hlam, p17578_0]
                                · linarith only [h0, h17597, hlam]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [h17469, hlam, p17578_1]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [hlam, p17578_0]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [h12794, hc01, hc13, hlam, hphi, p17578_1]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [h12794, h17469, h17474, hc01, hc12, hlam, hphi, p17578_1]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [h17474, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p17578_1]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [h17470, hlam, p17578_1]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [h17472, hlam, p17578_0]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [hlam, p17578_0]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [h17474, hlam, p17578_1]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              rcases p17578_3 (m.d 0 1) (by simp) with h17613 | h17613
                              · linarith only [h17613, hlam, p17578_0]
                              · rcases p17578_3 (m.d 1 2) (by simp) with h17615 | h17615
                                · rcases p17578_3 (m.d 1 3) (by simp) with h17616 | h17616
                                  · rcases p17578_3 (m.d 1 4) (by simp) with h17617 | h17617
                                    · linarith only [h17474, h17617, hlam]
                                    · linarith only [h12794, h17617, hlam]
                                  · linarith only [h11385, h17616, hlam]
                                · linarith only [h0, h17615, hlam]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [h17471, hlam, p17578_1]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [h17473, hlam, p17578_0]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [h12794, hc01, hc15, hlam, hphi, p17578_1]
                            · have p17578_0 := h17578c.1
                              have p17578_1 := h17578c.2.1
                              have p17578_2 := h17578c.2.2.1
                              have p17578_3 := h17578c.2.2.2
                              linarith only [hlam, p17578_0]
                      · linarith only [h14856, h17362, h17364, h17573, hc03, hc24, hlam, hphi, ht0b, ht45, ht5b]
                    · linarith only [h14856, h17363, h17572, hlam]
                · linarith only [h11385, h14856, h17364, h17473, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h14856, h17362, h17363, h17469, h17472, hlam]
            · linarith only [h14856, h17469, h17471, hc02, hc25, hlam, hphi]
          · linarith only [h14856, h17362, h17469, h17470, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h17632 | h17632
          · rcases m.htr 1 2 5 (by decide) (by decide) with h17633 | h17633
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17634 | h17634
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17635 | h17635
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17636 | h17636
                  · linarith only [h12794, h17365, h17469, h17632, h17636, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17638 | h17638
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17639 | h17639
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h17640 | h17640
                        · linarith only [h12794, h17636, h17640, hc01, hc24, hlam, hphi, ht12]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h17642 | h17642
                          · linarith only [h0, h12794, h17362, h17469, h17636, h17638, h17642, hc01, hc23, hlam, hphi, ht12]
                          · rcases h1bigk with h17644c | h17644c | h17644c | h17644c | h17644c | h17644c | h17644c | h17644c | h17644c | h17644c | h17644c | h17644c | h17644c | h17644c | h17644c | h17644c | h17644c | h17644c | h17644c | h17644c | h17644c | h17644c | h17644c | h17644c | h17644c
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [hlam, p17644_0]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [h0, hlam, p17644_0]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [h11385, hlam, p17644_0]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [h12794, hlam, p17644_0]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [h13812, hlam, p17644_0]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [h17469, hc01, hc23, hlam, hphi, ht12, p17644_1]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [hlam, p17644_0]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [h17469, hlam, p17644_0]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [h12794, h17469, hc01, hc23, hlam, hphi, ht12, p17644_1]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [h13812, h17469, hc01, hc23, hlam, hphi, ht12, p17644_1]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              rcases p17644_3 (m.d 0 1) (by simp) with h17655 | h17655
                              · linarith only [h17655, hlam, p17644_0]
                              · rcases p17644_3 (m.d 1 2) (by simp) with h17657 | h17657
                                · linarith only [h17469, h17657, hlam]
                                · linarith only [h0, h17657, hlam]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [h0, h17469, hc01, hc23, hlam, hphi, ht12, p17644_1]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [hlam, p17644_0]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [h12794, h17469, hc01, hc23, hlam, hphi, ht12, p17644_1]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [h12794, h17469, h17636, hc01, hc23, hlam, hphi, ht12, p17644_1]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [h17636, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p17644_1]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [h17632, hlam, p17644_1]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [h17634, hlam, p17644_0]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [hlam, p17644_0]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [h17636, hlam, p17644_1]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [h17469, h17633, hc01, hc23, hlam, hphi, ht12, p17644_1]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [h17633, hlam, p17644_1]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [h17635, hlam, p17644_0]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [h12794, h17469, h17633, hc01, hc23, hlam, hphi, ht12, p17644_1]
                            · have p17644_0 := h17644c.1
                              have p17644_1 := h17644c.2.1
                              have p17644_2 := h17644c.2.2.1
                              have p17644_3 := h17644c.2.2.2
                              linarith only [hlam, p17644_0]
                      · linarith only [h0, h17469, h17639, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h0, h17469, h17638, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h11385, h13812, h17364, h17469, h17633, h17635, hc01, hc23, hlam, hphi, ht12]
              · linarith only [h11385, h17363, h17634, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17678 | h17678
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17679 | h17679
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17680 | h17680
                  · linarith only [h12794, h17365, h17469, h17632, h17680, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17682 | h17682
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17683 | h17683
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h17684 | h17684
                        · linarith only [h0, h17362, h17633, h17680, h17683, h17684, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h17686 | h17686
                          · linarith only [h0, h17633, h17684, h17686, hc01, hc34, hlam, hphi, ht12, ht23]
                          · rcases h1bigk with h17688c | h17688c | h17688c | h17688c | h17688c | h17688c | h17688c | h17688c | h17688c | h17688c | h17688c | h17688c | h17688c | h17688c | h17688c | h17688c | h17688c | h17688c | h17688c | h17688c | h17688c | h17688c | h17688c | h17688c | h17688c
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [hlam, p17688_0]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [h0, hlam, p17688_0]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [h11385, hlam, p17688_0]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [h12794, hlam, p17688_0]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [h13812, hlam, p17688_0]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [h17633, hc01, hc25, hlam, hphi, ht12, p17688_1]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [hlam, p17688_0]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [h17469, hlam, p17688_0]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [h12794, h17633, h17684, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p17688_1]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [h17633, hlam, p17688_0]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              rcases p17688_3 (m.d 0 1) (by simp) with h17699 | h17699
                              · linarith only [h17699, hlam, p17688_0]
                              · rcases p17688_3 (m.d 1 2) (by simp) with h17701 | h17701
                                · linarith only [h17469, h17701, hlam]
                                · linarith only [h0, h17701, hlam]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [h0, h17469, hc01, hc23, hlam, hphi, ht12, p17688_1]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [hlam, p17688_0]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [h12794, h17469, hc01, hc23, hlam, hphi, ht12, p17688_1]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [h12794, h17469, h17632, h17633, hc01, hc23, hlam, hphi, ht12, p17688_1]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [h17469, h17632, hc01, hc23, hlam, hphi, ht12, p17688_1]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [h17632, hlam, p17688_1]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [h17678, hlam, p17688_0]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [hlam, p17688_0]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [h17680, hlam, p17688_1]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              rcases p17688_3 (m.d 0 1) (by simp) with h17713 | h17713
                              · linarith only [h17713, hlam, p17688_0]
                              · rcases p17688_3 (m.d 1 2) (by simp) with h17715 | h17715
                                · linarith only [h17633, h17715, hlam]
                                · linarith only [h0, h17715, hlam]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p17688_1]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [h17679, hlam, p17688_0]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [h12794, h17633, h17684, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p17688_1]
                            · have p17688_0 := h17688c.1
                              have p17688_1 := h17688c.2.1
                              have p17688_2 := h17688c.2.2.1
                              have p17688_3 := h17688c.2.2.2
                              linarith only [hlam, p17688_0]
                      · linarith only [h11385, h17364, h17469, h17683, hlam]
                    · linarith only [h12794, h17469, h17632, h17682, hc01, hc34, hlam, hphi, ht12, ht23]
                · linarith only [h11385, h17364, h17679, hlam]
              · linarith only [h11385, h17363, h17678, hlam]
          · linarith only [h0, h17362, h17632, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h17727 | h17727
      · linarith only [h14856, h17362, h17364, h17727, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h17729 | h17729
        · rcases m.htr 1 2 4 (by decide) (by decide) with h17730 | h17730
          · rcases m.htr 1 2 5 (by decide) (by decide) with h17731 | h17731
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17732 | h17732
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17733 | h17733
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17734 | h17734
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17735 | h17735
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17736 | h17736
                      · linarith only [h14856, h17362, h17364, h17729, h17736, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                      · linarith only [h14856, h17362, h17729, h17733, h17735, h17736, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h14856, h17363, h17735, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17740 | h17740
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17741 | h17741
                      · linarith only [h11385, h17364, h17729, h17741, hc01, hc12, hlam, hphi]
                      · linarith only [h14856, h17362, h17729, h17733, h17740, h17741, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · linarith only [h14856, h17363, h17740, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17745 | h17745
                  · linarith only [h12794, h17727, h17732, h17733, h17745, hc01, hc35, hlam, hphi, ht12, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17747 | h17747
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17748 | h17748
                      · linarith only [h17729, h17733, h17748, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h17750 | h17750
                        · linarith only [h12794, h17362, h17745, h17750, hc01, hc02, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h17752 | h17752
                          · linarith only [h12794, h14856, h17362, h17729, h17733, h17745, h17747, h17752, hc01, hc35, hlam, hphi, ht12, ht23]
                          · linarith only [h14856, h17362, h17729, h17733, h17747, h17752, hc34, hc45, hlam, hphi]
                    · linarith only [h14856, h17363, h17747, hlam]
              · linarith only [h14856, h17362, h17363, h17729, h17732, hlam]
            · linarith only [h14856, h17729, h17731, hc02, hc25, hlam, hphi]
          · linarith only [h14856, h17362, h17729, h17730, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h17759 | h17759
          · rcases m.htr 1 2 5 (by decide) (by decide) with h17760 | h17760
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17761 | h17761
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17762 | h17762
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17763 | h17763
                  · linarith only [h12794, h17727, h17729, h17759, h17763, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17765 | h17765
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17766 | h17766
                      · linarith only [h14856, h17362, h17364, h17729, h17760, h17765, h17766, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h17729, h17766, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h14856, h17364, h17729, h17760, h17762, h17765, hc02, hc34, hlam, hphi, ht23]
                · linarith only [h17729, h17760, h17762, hlam]
              · linarith only [h11385, h17363, h17761, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h17772 | h17772
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17773 | h17773
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17774 | h17774
                  · linarith only [h12794, h17727, h17729, h17759, h17774, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17776 | h17776
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17777 | h17777
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h17778 | h17778
                        · linarith only [h14856, h17362, h17364, h17729, h17773, h17774, h17778, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h17780 | h17780
                          · linarith only [h14856, h17362, h17364, h17729, h17760, h17773, h17776, h17778, h17780, hc12, hc23, hlam, hphi]
                          · rcases h1bigk with h17782c | h17782c | h17782c | h17782c | h17782c | h17782c | h17782c | h17782c | h17782c | h17782c | h17782c | h17782c | h17782c | h17782c | h17782c | h17782c | h17782c | h17782c | h17782c | h17782c | h17782c | h17782c | h17782c | h17782c | h17782c
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [hlam, p17782_0]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [h0, hlam, p17782_0]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [h11385, hlam, p17782_0]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [h12794, hlam, p17782_0]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [h13812, hlam, p17782_0]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [h17760, hc01, hc25, hlam, hphi, ht12, p17782_1]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [hlam, p17782_0]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [h17729, hlam, p17782_0]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [h12794, h14856, h17362, h17364, h17729, h17760, h17773, h17776, h17778, hc01, hc23, hc34, hc45, hlam, hphi, ht12, p17782_1]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [h17760, hlam, p17782_0]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              rcases p17782_3 (m.d 0 1) (by simp) with h17793 | h17793
                              · linarith only [h17793, hlam, p17782_0]
                              · rcases p17782_3 (m.d 1 2) (by simp) with h17795 | h17795
                                · linarith only [h17729, h17795, hlam]
                                · linarith only [h0, h17795, hlam]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [h0, h17729, hc01, hc23, hlam, hphi, ht12, p17782_1]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [hlam, p17782_0]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [h12794, h17729, hc01, hc23, hlam, hphi, ht12, p17782_1]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [h14856, h17362, h17364, h17729, h17773, h17776, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p17782_1]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [h17729, h17759, hc01, hc23, hlam, hphi, ht12, p17782_1]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [h17759, hlam, p17782_1]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [h17772, hlam, p17782_0]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [hlam, p17782_0]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [h17774, hlam, p17782_1]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              rcases p17782_3 (m.d 0 1) (by simp) with h17807 | h17807
                              · linarith only [h17807, hlam, p17782_0]
                              · rcases p17782_3 (m.d 1 2) (by simp) with h17809 | h17809
                                · linarith only [h17760, h17809, hlam]
                                · linarith only [h0, h17809, hlam]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [h0, hc01, hc15, hlam, hphi, p17782_1]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [h17773, hlam, p17782_0]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [h12794, h17760, h17778, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p17782_1]
                            · have p17782_0 := h17782c.1
                              have p17782_1 := h17782c.2.1
                              have p17782_2 := h17782c.2.2.1
                              have p17782_3 := h17782c.2.2.2
                              linarith only [hlam, p17782_0]
                      · linarith only [h17729, h17773, h17777, hlam]
                    · linarith only [h14856, h17362, h17364, h17729, h17773, h17776, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h17818 | h17818
                  · linarith only [h12794, h17727, h17729, h17759, h17818, hc01, hc23, hlam, hphi, ht12]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h17820 | h17820
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h17821 | h17821
                      · linarith only [h0, h17729, h17773, h17821, hc01, hc23, hlam, hphi, ht12]
                      · linarith only [h12794, h17729, h17759, h17821, hc01, hc35, hlam, hphi, ht12, ht23]
                    · linarith only [h12794, h17729, h17759, h17820, hc01, hc34, hlam, hphi, ht12, ht23]
              · linarith only [h11385, h17363, h17772, hlam]
          · linarith only [h0, h17362, h17759, hlam]
  · linarith only [h14856, h17362, h17363, hlam]

end R2N4
