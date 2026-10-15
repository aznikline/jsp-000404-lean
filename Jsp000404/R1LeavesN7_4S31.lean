import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_4S17
import Jsp000404.R1LeavesN7_4S29
import Jsp000404.R1LeavesN7_4S30

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 15022000 in
set_option maxHeartbeats 15022000 in
theorem r1l7_11_23_L_I_H_I_s11_x0_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h11385 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h11386 : (m.d 1 4 + m.lam ≤ m.d 0 1 ∧ m.d 1 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 1))
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
  rcases m.htr 0 1 5 (by decide) (by decide) with h12327 | h12327
  · rcases m.htr 0 2 3 (by decide) (by decide) with h12328 | h12328
    · rcases m.htr 0 2 4 (by decide) (by decide) with h12329 | h12329
      · rcases m.htr 0 3 4 (by decide) (by decide) with h12330 | h12330
        · linarith only [h11385, h11386, h12330, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h12332 | h12332
          · rcases m.htr 0 4 5 (by decide) (by decide) with h12333 | h12333
            · rcases m.htr 1 2 3 (by decide) (by decide) with h12334 | h12334
              · rcases m.htr 1 2 4 (by decide) (by decide) with h12335 | h12335
                · rcases m.htr 1 2 5 (by decide) (by decide) with h12336 | h12336
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h12337 | h12337
                    · linarith only [h11385, h11386, h12330, h12332, h12335, h12337, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h12339 | h12339
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h12340 | h12340
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12341 | h12341
                          · linarith only [h11385, h11386, h12334, h12337, h12341, hlam]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h12343 | h12343
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h12344 | h12344
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h12345 | h12345
                                · rcases h1bigk with h12346c | h12346c | h12346c | h12346c | h12346c | h12346c | h12346c | h12346c | h12346c | h12346c | h12346c | h12346c | h12346c | h12346c | h12346c | h12346c | h12346c | h12346c | h12346c | h12346c | h12346c | h12346c | h12346c | h12346c | h12346c
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [hlam, p12346_0]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [h0, hlam, p12346_0]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [h11386, h12334, h12343, h12345, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p12346_1]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [h11386, hlam, p12346_0]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    rcases p12346_3 (m.d 0 1) (by simp) with h12351 | h12351
                                    · rcases p12346_3 (m.d 1 2) (by simp) with h12352 | h12352
                                      · rcases p12346_3 (m.d 1 3) (by simp) with h12353 | h12353
                                        · linarith only [h11385, h12353, hlam]
                                        · linarith only [h12339, h12353, hlam]
                                      · linarith only [h12336, h12352, hlam]
                                    · linarith only [h12351, hlam, p12346_0]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [h11385, h12334, h12343, h12345, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p12346_1]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [hlam, p12346_0]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    rcases p12346_3 (m.d 0 1) (by simp) with h12360 | h12360
                                    · linarith only [h0, h12360, hlam]
                                    · linarith only [h11385, h12360, hlam]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [h11385, h11386, h12334, h12343, h12345, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p12346_1]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    rcases p12346_3 (m.d 0 1) (by simp) with h12364 | h12364
                                    · linarith only [h0, h12364, hlam]
                                    · linarith only [h12327, h12364, hlam]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [h11385, hlam, p12346_0]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [h12334, hlam, p12346_1]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [hlam, p12346_0]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [h12337, hlam, p12346_1]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [h11385, h11386, h12335, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p12346_1]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [h11385, h12334, h12335, h12343, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p12346_1]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [h12335, hlam, p12346_1]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    rcases p12346_3 (m.d 0 1) (by simp) with h12374 | h12374
                                    · linarith only [h11386, h12374, hlam]
                                    · linarith only [h11385, h12374, hlam]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [hlam, p12346_0]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    rcases p12346_3 (m.d 0 1) (by simp) with h12378 | h12378
                                    · linarith only [h11386, h12378, hlam]
                                    · linarith only [h12327, h12378, hlam]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [h12327, hlam, p12346_0]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [h12336, hlam, p12346_1]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [h12339, hlam, p12346_0]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [h12340, hlam, p12346_0]
                                  · have p12346_0 := h12346c.1
                                    have p12346_1 := h12346c.2.1
                                    have p12346_2 := h12346c.2.2.1
                                    have p12346_3 := h12346c.2.2.2
                                    linarith only [hlam, p12346_0]
                                · linarith only [h11385, h11386, h12337, h12345, hc13, hc45, hlam, hphi, ht34]
                              · linarith only [h11385, h11386, h12337, h12339, h12340, h12341, h12344, hc23, hc34, hlam, hphi]
                            · linarith only [h11385, h11386, h12332, h12337, h12343, hc23, hc34, hlam, hphi]
                        · linarith only [h11385, h11386, h12340, hc13, hc45, hlam, hphi, ht34]
                      · linarith only [h11385, h11386, h12332, h12337, h12339, hc13, hc34, hlam, hphi]
                  · linarith only [h11386, h12327, h12335, h12336, hlam]
                · linarith only [h0, h11385, h12329, h12334, h12335, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h12328, h12334, hlam]
            · linarith only [h11385, h11386, h12332, h12333, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h12395 | h12395
            · rcases m.htr 1 2 3 (by decide) (by decide) with h12396 | h12396
              · rcases m.htr 1 2 4 (by decide) (by decide) with h12397 | h12397
                · rcases m.htr 1 2 5 (by decide) (by decide) with h12398 | h12398
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h12399 | h12399
                    · linarith only [h11385, h11386, h12330, h12399, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h12401 | h12401
                      · linarith only [h11385, h12332, h12401, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h12403 | h12403
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12404 | h12404
                          · linarith only [h11386, h12327, h12328, h12399, h12401, h12404, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h12406 | h12406
                            · linarith only [h11385, h12332, h12396, h12406, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h12408 | h12408
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h12409 | h12409
                                · rcases h1bigk with h12410c | h12410c | h12410c | h12410c | h12410c | h12410c | h12410c | h12410c | h12410c | h12410c | h12410c | h12410c | h12410c | h12410c | h12410c | h12410c | h12410c | h12410c | h12410c | h12410c | h12410c | h12410c | h12410c | h12410c | h12410c
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [hlam, p12410_0]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [h0, hlam, p12410_0]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [h11386, h12396, h12399, hc23, hc34, hlam, hphi, p12410_1]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [h11386, hlam, p12410_0]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [h11386, h12396, h12399, h12401, hc23, hc34, hlam, hphi, p12410_1]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    rcases p12410_3 (m.d 0 1) (by simp) with h12416 | h12416
                                    · linarith only [h12416, hlam, p12410_0]
                                    · rcases p12410_3 (m.d 1 2) (by simp) with h12418 | h12418
                                      · rcases p12410_3 (m.d 1 3) (by simp) with h12419 | h12419
                                        · linarith only [h12396, h12419, hlam]
                                        · rcases p12410_3 (m.d 1 4) (by simp) with h12421 | h12421
                                          · linarith only [h12397, h12421, hlam]
                                          · linarith only [h11386, h12421, hlam]
                                      · linarith only [h12418, hlam, p12410_0]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [hlam, p12410_0]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    rcases p12410_3 (m.d 0 1) (by simp) with h12426 | h12426
                                    · linarith only [h0, h12426, hlam]
                                    · linarith only [h11385, h12426, hlam]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [h11386, h12327, h12396, h12401, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12410_1]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    rcases p12410_3 (m.d 0 1) (by simp) with h12430 | h12430
                                    · linarith only [h0, h12430, hlam]
                                    · linarith only [h12327, h12430, hlam]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [h11385, hlam, p12410_0]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [h12396, hlam, p12410_1]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [hlam, p12410_0]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [h12399, hlam, p12410_1]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [h12401, hlam, p12410_1]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [h12327, h12396, h12399, h12401, hc23, hc34, hlam, hphi, p12410_1]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [h12397, hlam, p12410_1]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    rcases p12410_3 (m.d 0 1) (by simp) with h12440 | h12440
                                    · linarith only [h11386, h12440, hlam]
                                    · linarith only [h11385, h12440, hlam]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [hlam, p12410_0]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    rcases p12410_3 (m.d 0 1) (by simp) with h12444 | h12444
                                    · linarith only [h11386, h12444, hlam]
                                    · linarith only [h12327, h12444, hlam]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [h12327, hlam, p12410_0]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [h12398, hlam, p12410_1]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [h0, h12327, h12396, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12410_1]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [h12403, hlam, p12410_0]
                                  · have p12410_0 := h12410c.1
                                    have p12410_1 := h12410c.2.1
                                    have p12410_2 := h12410c.2.2.1
                                    have p12410_3 := h12410c.2.2.2
                                    linarith only [hlam, p12410_0]
                                · linarith only [h11386, h12327, h12398, h12399, h12408, h12409, hlam]
                              · linarith only [h11386, h12327, h12399, h12403, h12404, h12408, hc23, hc34, hlam, hphi]
                        · linarith only [h11385, h11386, h12396, h12403, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h11386, h12327, h12397, h12398, hlam]
                · linarith only [h0, h12329, h12397, hlam]
              · linarith only [h0, h12328, h12396, hlam]
            · linarith only [h11386, h12327, h12395, hlam]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h12459 | h12459
        · linarith only [h0, h11385, h12329, h12459, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h12461 | h12461
          · rcases m.htr 0 4 5 (by decide) (by decide) with h12462 | h12462
            · rcases m.htr 1 2 3 (by decide) (by decide) with h12463 | h12463
              · rcases m.htr 1 2 4 (by decide) (by decide) with h12464 | h12464
                · rcases m.htr 1 2 5 (by decide) (by decide) with h12465 | h12465
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h12466 | h12466
                    · linarith only [h0, h11385, h12329, h12459, h12464, h12466, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h12468 | h12468
                      · linarith only [h0, h11385, h12329, h12464, h12468, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · linarith only [h0, h11385, h12329, h12461, h12463, h12464, h12468, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                  · linarith only [h0, h12329, h12464, h12465, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h12472 | h12472
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h12473 | h12473
                    · linarith only [h11385, h12459, h12461, h12473, hc01, hc35, hlam, hphi, ht0b, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h12475 | h12475
                      · linarith only [h0, h11385, h12464, h12475, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · linarith only [h0, h11385, h12461, h12463, h12464, h12475, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h0, h12327, h12472, hlam]
              · linarith only [h0, h11386, h12328, h12329, h12463, hc01, hc14, hlam, hphi]
            · linarith only [h0, h11385, h12329, h12461, h12462, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h12481 | h12481
            · rcases m.htr 1 2 3 (by decide) (by decide) with h12482 | h12482
              · rcases m.htr 1 2 4 (by decide) (by decide) with h12483 | h12483
                · rcases m.htr 1 2 5 (by decide) (by decide) with h12484 | h12484
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h12485 | h12485
                    · linarith only [h0, h11385, h12329, h12483, h12485, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h12487 | h12487
                      · linarith only [h0, h11385, h12329, h12461, h12483, h12487, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h12489 | h12489
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12490 | h12490
                          · linarith only [h0, h11385, h12329, h12482, h12483, h12485, h12490, hc12, hc14, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h12492 | h12492
                            · linarith only [h0, h12327, h12329, h12461, h12482, h12483, h12487, h12492, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h12494 | h12494
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h12495 | h12495
                                · rcases h1bigk with h12496c | h12496c | h12496c | h12496c | h12496c | h12496c | h12496c | h12496c | h12496c | h12496c | h12496c | h12496c | h12496c | h12496c | h12496c | h12496c | h12496c | h12496c | h12496c | h12496c | h12496c | h12496c | h12496c | h12496c | h12496c
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [hlam, p12496_0]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [h0, hlam, p12496_0]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [h0, h12329, h12483, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12496_1]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [h11386, hlam, p12496_0]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [h0, h12329, h12483, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b, p12496_1]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    rcases p12496_3 (m.d 0 1) (by simp) with h12502 | h12502
                                    · linarith only [h12502, hlam, p12496_0]
                                    · rcases p12496_3 (m.d 1 2) (by simp) with h12504 | h12504
                                      · rcases p12496_3 (m.d 1 3) (by simp) with h12505 | h12505
                                        · linarith only [h12482, h12505, hlam]
                                        · rcases p12496_3 (m.d 1 4) (by simp) with h12507 | h12507
                                          · linarith only [h12483, h12507, hlam]
                                          · linarith only [h11386, h12507, hlam]
                                      · linarith only [h12504, hlam, p12496_0]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [hlam, p12496_0]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [h0, h11385, h12329, h12483, hlam, p12496_2]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [h0, h12329, h12483, hc01, hc12, hlam, hphi, p12496_1]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [h0, h12327, h12329, h12483, hlam, p12496_2]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [h11385, hlam, p12496_0]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [h12482, hlam, p12496_1]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [hlam, p12496_0]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [h12485, hlam, p12496_1]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [h12487, hlam, p12496_1]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [h12327, h12484, h12485, h12492, hc23, hc34, hlam, hphi, p12496_1]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [h12483, hlam, p12496_1]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    rcases p12496_3 (m.d 0 1) (by simp) with h12522 | h12522
                                    · linarith only [h11386, h12522, hlam]
                                    · linarith only [h11385, h12522, hlam]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [hlam, p12496_0]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    rcases p12496_3 (m.d 0 1) (by simp) with h12526 | h12526
                                    · linarith only [h11386, h12526, hlam]
                                    · linarith only [h12327, h12526, hlam]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [h12327, hlam, p12496_0]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [h12484, hlam, p12496_1]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [h0, h12327, h12329, h12482, h12483, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12496_1]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [h12489, hlam, p12496_0]
                                  · have p12496_0 := h12496c.1
                                    have p12496_1 := h12496c.2.1
                                    have p12496_2 := h12496c.2.2.1
                                    have p12496_3 := h12496c.2.2.2
                                    linarith only [hlam, p12496_0]
                                · linarith only [h11385, h11386, h12482, h12485, h12495, hc23, hc45, hlam, hphi, ht34]
                              · linarith only [h0, h12327, h12329, h12489, h12494, hc02, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                        · linarith only [h11386, h12327, h12481, h12489, hlam]
                  · linarith only [h0, h12329, h12483, h12484, hc01, hc25, hlam, hphi, ht12]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h12538 | h12538
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h12539 | h12539
                    · linarith only [h0, h11385, h12483, h12539, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h12541 | h12541
                      · linarith only [h11385, h12461, h12541, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h12543 | h12543
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12544 | h12544
                          · linarith only [h0, h12327, h12482, h12483, h12539, h12541, h12544, hlam]
                          · linarith only [h0, h12327, h12483, h12541, h12544, hc13, hc34, hlam, hphi]
                        · linarith only [h0, h12327, h12482, h12483, h12541, h12543, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h12327, h12538, hlam]
              · linarith only [h0, h12327, h12328, h12329, h12482, hc04, hc15, hlam, hphi, ht0b, ht5b]
            · linarith only [h0, h12327, h12329, h12481, hlam]
    · linarith only [h0, h11385, h12328, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h12552 | h12552
    · rcases m.htr 0 2 4 (by decide) (by decide) with h12553 | h12553
      · rcases m.htr 0 3 4 (by decide) (by decide) with h12554 | h12554
        · linarith only [h11385, h11386, h12554, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h12556 | h12556
          · linarith only [h11385, h12327, h12556, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h12558 | h12558
            · rcases m.htr 1 2 3 (by decide) (by decide) with h12559 | h12559
              · rcases m.htr 1 2 4 (by decide) (by decide) with h12560 | h12560
                · rcases m.htr 1 2 5 (by decide) (by decide) with h12561 | h12561
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h12562 | h12562
                    · linarith only [h11385, h12327, h12554, h12562, hc03, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h12564 | h12564
                      · linarith only [h11385, h12327, h12556, h12564, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h12566 | h12566
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12567 | h12567
                          · linarith only [h11385, h12327, h12552, h12562, h12566, h12567, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h12569 | h12569
                            · linarith only [h11385, h12327, h12559, h12564, h12569, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h12571 | h12571
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h12572 | h12572
                                · rcases h1bigk with h12573c | h12573c | h12573c | h12573c | h12573c | h12573c | h12573c | h12573c | h12573c | h12573c | h12573c | h12573c | h12573c | h12573c | h12573c | h12573c | h12573c | h12573c | h12573c | h12573c | h12573c | h12573c | h12573c | h12573c | h12573c
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [hlam, p12573_0]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [h0, hlam, p12573_0]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [h12327, h12559, h12562, h12566, hc23, hc34, hlam, hphi, p12573_1]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [h11386, hlam, p12573_0]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [h12327, hlam, p12573_0]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    rcases p12573_3 (m.d 0 1) (by simp) with h12579 | h12579
                                    · linarith only [h12579, hlam, p12573_0]
                                    · rcases p12573_3 (m.d 1 2) (by simp) with h12581 | h12581
                                      · rcases p12573_3 (m.d 1 3) (by simp) with h12582 | h12582
                                        · linarith only [h12559, h12582, hlam]
                                        · rcases p12573_3 (m.d 1 4) (by simp) with h12584 | h12584
                                          · linarith only [h12560, h12584, hlam]
                                          · linarith only [h11386, h12584, hlam]
                                      · linarith only [h12581, hlam, p12573_0]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [hlam, p12573_0]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    rcases p12573_3 (m.d 0 1) (by simp) with h12589 | h12589
                                    · linarith only [h0, h12589, hlam]
                                    · linarith only [h11385, h12589, hlam]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [h11386, hc01, hc12, hlam, hphi, p12573_1]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [h11385, h12327, h12559, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12573_1]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [h11385, hlam, p12573_0]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [h12559, hlam, p12573_1]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [hlam, p12573_0]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [h12562, hlam, p12573_1]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [h12564, hlam, p12573_1]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [h11385, h12559, h12562, hc23, hc34, hlam, hphi, p12573_1]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [h12560, hlam, p12573_1]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    rcases p12573_3 (m.d 0 1) (by simp) with h12601 | h12601
                                    · linarith only [h11386, h12601, hlam]
                                    · linarith only [h11385, h12601, hlam]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [hlam, p12573_0]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [h11385, h12327, h12559, h12562, hc23, hc34, hlam, hphi, p12573_1]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [h11385, h12559, h12564, hc23, hc35, hlam, hphi, p12573_1]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [h12561, hlam, p12573_1]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    rcases p12573_3 (m.d 0 1) (by simp) with h12608 | h12608
                                    · linarith only [h12327, h12608, hlam]
                                    · linarith only [h11385, h12608, hlam]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [h12566, hlam, p12573_0]
                                  · have p12573_0 := h12573c.1
                                    have p12573_1 := h12573c.2.1
                                    have p12573_2 := h12573c.2.2.1
                                    have p12573_3 := h12573c.2.2.2
                                    linarith only [hlam, p12573_0]
                                · linarith only [h11385, h11386, h12553, h12562, h12571, h12572, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h12614 | h12614
                                · rcases h1bigk with h12615c | h12615c | h12615c | h12615c | h12615c | h12615c | h12615c | h12615c | h12615c | h12615c | h12615c | h12615c | h12615c | h12615c | h12615c | h12615c | h12615c | h12615c | h12615c | h12615c | h12615c | h12615c | h12615c | h12615c | h12615c
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [hlam, p12615_0]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [h0, hlam, p12615_0]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [h11386, h12559, h12562, hc23, hc34, hlam, hphi, p12615_1]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [h11386, hlam, p12615_0]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [h12327, hlam, p12615_0]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    rcases p12615_3 (m.d 0 1) (by simp) with h12621 | h12621
                                    · linarith only [h12621, hlam, p12615_0]
                                    · rcases p12615_3 (m.d 1 2) (by simp) with h12623 | h12623
                                      · rcases p12615_3 (m.d 1 3) (by simp) with h12624 | h12624
                                        · linarith only [h12559, h12624, hlam]
                                        · rcases p12615_3 (m.d 1 4) (by simp) with h12626 | h12626
                                          · linarith only [h12560, h12626, hlam]
                                          · linarith only [h11386, h12626, hlam]
                                      · linarith only [h12623, hlam, p12615_0]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [hlam, p12615_0]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    rcases p12615_3 (m.d 0 1) (by simp) with h12631 | h12631
                                    · linarith only [h0, h12631, hlam]
                                    · linarith only [h11385, h12631, hlam]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [h11386, h12558, h12571, hc12, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p12615_1]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [h12327, hc01, hc12, hlam, hphi, p12615_1]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [h11385, hlam, p12615_0]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [h12559, hlam, p12615_1]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [hlam, p12615_0]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [h12562, hlam, p12615_1]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [h12564, hlam, p12615_1]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [h11385, h12559, h12562, hc23, hc34, hlam, hphi, p12615_1]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [h12560, hlam, p12615_1]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    rcases p12615_3 (m.d 0 1) (by simp) with h12643 | h12643
                                    · linarith only [h11386, h12643, hlam]
                                    · linarith only [h11385, h12643, hlam]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [hlam, p12615_0]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [h11385, h12327, h12559, h12562, hc23, hc34, hlam, hphi, p12615_1]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [h11385, h12559, h12564, hc23, hc35, hlam, hphi, p12615_1]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [h12561, hlam, p12615_1]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    rcases p12615_3 (m.d 0 1) (by simp) with h12650 | h12650
                                    · linarith only [h12327, h12650, hlam]
                                    · linarith only [h11385, h12650, hlam]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [h12566, hlam, p12615_0]
                                  · have p12615_0 := h12615c.1
                                    have p12615_1 := h12615c.2.1
                                    have p12615_2 := h12615c.2.2.1
                                    have p12615_3 := h12615c.2.2.2
                                    linarith only [hlam, p12615_0]
                                · linarith only [h11385, h11386, h12553, h12558, h12559, h12562, h12614, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                        · linarith only [h11386, h12558, h12566, hlam]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h12657 | h12657
                    · linarith only [h0, h11385, h12561, h12657, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h12659 | h12659
                      · linarith only [h11385, h11386, h12560, h12561, h12659, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h12661 | h12661
                        · linarith only [h12560, h12561, h12661, hlam]
                        · linarith only [h0, h11386, h12553, h12558, h12561, h12661, hc01, hc25, hlam, hphi, ht12]
                · linarith only [h0, h11385, h12553, h12559, h12560, hc02, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h12552, h12559, hlam]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h12666 | h12666
              · rcases m.htr 1 2 4 (by decide) (by decide) with h12667 | h12667
                · rcases m.htr 1 2 5 (by decide) (by decide) with h12668 | h12668
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h12669 | h12669
                    · linarith only [h11385, h11386, h12554, h12669, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h12671 | h12671
                      · linarith only [h11385, h11386, h12556, h12558, h12671, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h12673 | h12673
                        · linarith only [h11385, h11386, h12558, h12669, h12673, hc13, hc34, hlam, hphi]
                        · linarith only [h11385, h11386, h12666, h12673, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h12676 | h12676
                    · linarith only [h11385, h11386, h12667, h12668, h12676, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h12678 | h12678
                      · linarith only [h11385, h11386, h12667, h12668, h12678, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h12680 | h12680
                        · linarith only [h11385, h11386, h12558, h12666, h12667, h12668, h12680, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h11385, h11386, h12666, h12680, hc23, hc45, hlam, hphi, ht34]
                · linarith only [h0, h12553, h12667, hlam]
              · linarith only [h0, h11385, h12552, h12666, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
      · rcases m.htr 0 3 4 (by decide) (by decide) with h12685 | h12685
        · linarith only [h0, h11385, h12553, h12685, hlam]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h12687 | h12687
          · linarith only [h11385, h12327, h12687, hlam]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h12689 | h12689
            · rcases m.htr 1 2 3 (by decide) (by decide) with h12690 | h12690
              · rcases m.htr 1 2 4 (by decide) (by decide) with h12691 | h12691
                · rcases m.htr 1 2 5 (by decide) (by decide) with h12692 | h12692
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h12693 | h12693
                    · linarith only [h0, h11385, h12553, h12685, h12691, h12693, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h12695 | h12695
                      · linarith only [h11385, h12327, h12687, h12695, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h12697 | h12697
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12698 | h12698
                          · linarith only [h12327, h12552, h12553, h12691, h12693, h12697, h12698, hc01, hc12, hlam, hphi]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h12700 | h12700
                            · linarith only [h0, h11385, h12553, h12690, h12691, h12700, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h12702 | h12702
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h12703 | h12703
                                · rcases h1bigk with h12704c | h12704c | h12704c | h12704c | h12704c | h12704c | h12704c | h12704c | h12704c | h12704c | h12704c | h12704c | h12704c | h12704c | h12704c | h12704c | h12704c | h12704c | h12704c | h12704c | h12704c | h12704c | h12704c | h12704c | h12704c
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [hlam, p12704_0]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [h0, hlam, p12704_0]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [h0, h12553, h12690, h12691, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12704_1]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [h11386, hlam, p12704_0]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [h12327, hlam, p12704_0]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    rcases p12704_3 (m.d 0 1) (by simp) with h12710 | h12710
                                    · linarith only [h12710, hlam, p12704_0]
                                    · rcases p12704_3 (m.d 1 2) (by simp) with h12712 | h12712
                                      · rcases p12704_3 (m.d 1 3) (by simp) with h12713 | h12713
                                        · linarith only [h12690, h12713, hlam]
                                        · rcases p12704_3 (m.d 1 4) (by simp) with h12715 | h12715
                                          · linarith only [h12691, h12715, hlam]
                                          · linarith only [h11386, h12715, hlam]
                                      · linarith only [h12712, hlam, p12704_0]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [hlam, p12704_0]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [h0, h11385, h12553, h12691, hlam, p12704_2]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [h0, h12553, h12691, hc01, hc12, hlam, hphi, p12704_1]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [h11385, h12327, h12690, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p12704_1]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [h11385, hlam, p12704_0]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [h12690, hlam, p12704_1]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [hlam, p12704_0]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [h12693, hlam, p12704_1]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [h12695, hlam, p12704_1]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [h11385, h12690, h12693, hc23, hc34, hlam, hphi, p12704_1]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [h12691, hlam, p12704_1]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    rcases p12704_3 (m.d 0 1) (by simp) with h12730 | h12730
                                    · linarith only [h11386, h12730, hlam]
                                    · linarith only [h11385, h12730, hlam]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [hlam, p12704_0]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [h11385, h12327, h12690, h12693, hc23, hc34, hlam, hphi, p12704_1]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [h11385, h12690, h12695, hc23, hc35, hlam, hphi, p12704_1]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [h12692, hlam, p12704_1]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    rcases p12704_3 (m.d 0 1) (by simp) with h12737 | h12737
                                    · linarith only [h12327, h12737, hlam]
                                    · linarith only [h11385, h12737, hlam]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [h12697, hlam, p12704_0]
                                  · have p12704_0 := h12704c.1
                                    have p12704_1 := h12704c.2.1
                                    have p12704_2 := h12704c.2.2.1
                                    have p12704_3 := h12704c.2.2.2
                                    linarith only [hlam, p12704_0]
                                · linarith only [h11385, h11386, h12689, h12690, h12693, h12703, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                              · linarith only [h12553, h12689, h12702, hlam]
                        · linarith only [h12553, h12689, h12691, h12697, hlam]
                  · linarith only [h0, h11385, h12553, h12690, h12691, h12692, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h12746 | h12746
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h12747 | h12747
                    · linarith only [h11385, h12327, h12685, h12691, h12746, h12747, hc04, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h12749 | h12749
                      · linarith only [h11385, h12327, h12691, h12746, h12749, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h12751 | h12751
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12752 | h12752
                          · linarith only [h11385, h12327, h12690, h12691, h12746, h12747, h12752, hlam]
                          · linarith only [h11385, h12327, h12690, h12691, h12746, h12752, hc23, hc34, hlam, hphi]
                        · linarith only [h11385, h12327, h12689, h12690, h12691, h12746, h12751, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h12756 | h12756
                    · linarith only [h0, h11385, h12685, h12746, h12756, hc04, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h12758 | h12758
                      · linarith only [h0, h11385, h12746, h12758, hc25, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h12760 | h12760
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h12761 | h12761
                          · linarith only [h0, h11385, h12690, h12746, h12756, h12761, hc14, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                          · linarith only [h0, h11385, h12690, h12691, h12761, hc23, hc34, hlam, hphi]
                        · linarith only [h11385, h11386, h12689, h12690, h12760, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b]
              · linarith only [h0, h11385, h12552, h12690, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h12766 | h12766
              · rcases m.htr 1 2 4 (by decide) (by decide) with h12767 | h12767
                · rcases m.htr 1 2 5 (by decide) (by decide) with h12768 | h12768
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h12769 | h12769
                    · linarith only [h0, h11385, h12553, h12767, h12769, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h12771 | h12771
                      · linarith only [h0, h11385, h12553, h12767, h12771, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h12773 | h12773
                        · linarith only [h11385, h11386, h12689, h12769, h12773, hc13, hc34, hlam, hphi]
                        · linarith only [h11385, h11386, h12766, h12773, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h11385, h12553, h12766, h12767, h12768, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                · rcases m.htr 1 2 5 (by decide) (by decide) with h12777 | h12777
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h12778 | h12778
                    · linarith only [h0, h11385, h12767, h12778, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h12780 | h12780
                      · linarith only [h11385, h12327, h12767, h12777, h12780, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h12782 | h12782
                        · linarith only [h0, h11385, h12553, h12689, h12766, h12778, h12782, hc23, hc34, hlam, hphi]
                        · linarith only [h11385, h11386, h12766, h12782, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h12785 | h12785
                    · linarith only [h0, h11385, h12767, h12785, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h12787 | h12787
                      · linarith only [h0, h11385, h12767, h12787, hc24, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h12789 | h12789
                        · linarith only [h0, h11385, h12553, h12689, h12766, h12785, h12789, hc23, hc34, hlam, hphi]
                        · linarith only [h11385, h11386, h12766, h12789, hc23, hc45, hlam, hphi, ht34]
              · linarith only [h0, h11385, h12552, h12553, h12689, h12766, hc05, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
    · linarith only [h0, h11385, h12552, hlam]

set_option maxHeartbeats 15022000 in
set_option maxHeartbeats 15022000 in
theorem r1l7_11_23_L_I_H_I_s11_x0 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h11385 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  rcases m.htr 0 1 4 (by decide) (by decide) with h11386 | h11386
  · exact r1l7_11_23_L_I_H_I_s11_x0_x0 m hb1 hb3 hg0 h11385 h11386
  · exact r1l7_11_23_L_I_H_I_s11_x0_x1 m hb1 hb3 hg0 h11385 h11386

set_option maxHeartbeats 15022000 in
set_option maxHeartbeats 15022000 in
theorem r1l7_11_23_L_I_H_I_s11_x1 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hg0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h11385 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
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
  exact r1l7_11_23_L_I_H_I_s12 m hb1 hb3 h0 h11385

set_option maxHeartbeats 15022000 in
set_option maxHeartbeats 15022000 in
theorem r1l7_11_23_L_I_H_I_s11 (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h0 := hg0
  rcases m.htr 0 1 3 (by decide) (by decide) with h11385 | h11385
  · exact r1l7_11_23_L_I_H_I_s11_x0 m hb1 hb3 hg0 h11385
  · exact r1l7_11_23_L_I_H_I_s11_x1 m hb1 hb3 hg0 h11385

set_option maxHeartbeats 37792000 in
set_option maxHeartbeats 37792000 in
theorem r1l7_11_23_L_I_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig2_7_H_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · exact r1l7_11_23_L_I_H_I_s0 m hb1 hb3 h0
  · exact r1l7_11_23_L_I_H_I_s11 m hb1 hb3 h0

end R2N4
