import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 15178000 in
set_option maxHeartbeats 15178000 in
theorem r1l7_10_12_13_25_L_R_L_I_L_I_H_I_s2_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (hg2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h6383 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0ehi := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u0ehi3 := h0ehi (m.d 0 4) (by simp)
  have u0ehi4 := h0ehi (m.d 0 5) (by simp)
  have h0 := hg0
  have h1 := hg1
  have h2 := hg2
  rcases m.htr 0 2 5 (by decide) (by decide) with h6384 | h6384
  · rcases m.htr 0 3 4 (by decide) (by decide) with h6385 | h6385
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6386 | h6386
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6387 | h6387
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6388 | h6388
          · linarith only [h0, h3, h6388, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6390 | h6390
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6391 | h6391
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6392 | h6392
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6393 | h6393
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6394 | h6394
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6395 | h6395
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6396 | h6396
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6397 | h6397
                          · rcases h2bigk with h6398c | h6398c | h6398c | h6398c | h6398c | h6398c | h6398c | h6398c | h6398c | h6398c | h6398c | h6398c | h6398c | h6398c | h6398c | h6398c | h6398c | h6398c | h6398c | h6398c | h6398c | h6398c | h6398c | h6398c | h6398c
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [hlam, p6398_0]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [h3, hc12, hc23, hlam, hphi, p6398_1]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [h3, hlam, p6398_0]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [h3, h6394, h6397, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6398_1]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              rcases p6398_3 (m.d 0 2) (by simp) with h6403 | h6403
                              · rcases p6398_3 (m.d 1 2) (by simp) with h6404 | h6404
                                · linarith only [h0, h6404, hlam]
                                · linarith only [h6390, h6404, hlam]
                              · linarith only [h6403, hlam, p6398_0]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [h0, hlam, p6398_0]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [hlam, p6398_0]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [h6388, hlam, p6398_0]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [h0, h6394, h6397, hc01, hc45, hlam, hphi, ht0b, ht5b, p6398_1]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              rcases p6398_3 (m.d 0 2) (by simp) with h6412 | h6412
                              · rcases p6398_3 (m.d 1 2) (by simp) with h6413 | h6413
                                · rcases p6398_3 (m.d 2 3) (by simp) with h6414 | h6414
                                  · rcases p6398_3 (m.d 2 4) (by simp) with h6415 | h6415
                                    · linarith only [h3, h6383, h6395, h6397, h6415, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6398_1]
                                    · linarith only [h6396, h6415, hlam]
                                  · linarith only [h6395, h6414, hlam]
                                · linarith only [h6413, hlam, p6398_0]
                              · linarith only [h6384, h6412, hlam]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [hc23, hlam, hphi, ht01, ht12, p6398_1, u0ehi1]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              rcases p6398_3 (m.d 0 2) (by simp) with h6422 | h6422
                              · linarith only [h3, h6422, hlam]
                              · linarith only [h0, h6422, hlam]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [hlam, p6398_0]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              rcases p6398_3 (m.d 0 2) (by simp) with h6426 | h6426
                              · linarith only [h3, h6426, hlam]
                              · linarith only [h6383, h6426, hlam]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              rcases p6398_3 (m.d 0 2) (by simp) with h6429 | h6429
                              · linarith only [h3, h6429, hlam]
                              · linarith only [h6384, h6429, hlam]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [h6383, hlam, p6398_0]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [h6383, h6390, hc02, hc25, hlam, hphi, ht0b, ht5b, p6398_1]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [h6394, hlam, p6398_1]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [hlam, p6398_0]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [h3, h6383, h6395, h6397, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p6398_1]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [h6384, hlam, p6398_0]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [h6390, hlam, p6398_0]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [h6395, hlam, p6398_1]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [h6396, hlam, p6398_0]
                            · have p6398_0 := h6398c.1
                              have p6398_1 := h6398c.2.1
                              have p6398_2 := h6398c.2.2.1
                              have p6398_3 := h6398c.2.2.2
                              linarith only [hlam, p6398_0]
                          · linarith only [h3, h6383, h6396, h6397, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6443 | h6443
                          · linarith only [h6394, h6396, h6443, hlam]
                          · rcases h2bigk with h6445c | h6445c | h6445c | h6445c | h6445c | h6445c | h6445c | h6445c | h6445c | h6445c | h6445c | h6445c | h6445c | h6445c | h6445c | h6445c | h6445c | h6445c | h6445c | h6445c | h6445c | h6445c | h6445c | h6445c | h6445c
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              linarith only [hlam, p6445_0]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              linarith only [h3, h6390, h6393, h6394, h6396, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6445_1]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              linarith only [h3, hlam, p6445_0]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              rcases p6445_3 (m.d 0 2) (by simp) with h6449 | h6449
                              · rcases p6445_3 (m.d 1 2) (by simp) with h6450 | h6450
                                · linarith only [h0, h6450, hlam]
                                · linarith only [h6390, h6393, h6396, h6450, hlam]
                              · linarith only [h6449, hlam, p6445_0]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              rcases p6445_3 (m.d 0 2) (by simp) with h6454 | h6454
                              · rcases p6445_3 (m.d 1 2) (by simp) with h6455 | h6455
                                · linarith only [h0, h6455, hlam]
                                · linarith only [h6390, h6455, hlam]
                              · linarith only [h6454, hlam, p6445_0]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              linarith only [h0, hlam, p6445_0]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              linarith only [hlam, p6445_0]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              linarith only [h6388, hlam, p6445_0]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              rcases p6445_3 (m.d 0 2) (by simp) with h6462 | h6462
                              · rcases p6445_3 (m.d 1 2) (by simp) with h6463 | h6463
                                · rcases p6445_3 (m.d 2 3) (by simp) with h6464 | h6464
                                  · rcases p6445_3 (m.d 2 4) (by simp) with h6465 | h6465
                                    · linarith only [h6465, hlam, p6445_0]
                                    · rcases p6445_3 (m.d 2 5) (by simp) with h6467 | h6467
                                      · linarith only [h6390, h6467, hlam]
                                      · linarith only [h6396, h6467, hlam]
                                  · linarith only [h6394, h6464, hlam]
                                · linarith only [h6463, hlam, p6445_0]
                              · linarith only [h6383, h6462, hlam]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              rcases p6445_3 (m.d 0 2) (by simp) with h6473 | h6473
                              · rcases p6445_3 (m.d 1 2) (by simp) with h6474 | h6474
                                · rcases p6445_3 (m.d 2 3) (by simp) with h6475 | h6475
                                  · rcases p6445_3 (m.d 2 4) (by simp) with h6476 | h6476
                                    · linarith only [h6396, h6476, hlam, p6445_1]
                                    · rcases p6445_3 (m.d 2 5) (by simp) with h6478 | h6478
                                      · linarith only [h6478, hlam, p6445_0]
                                      · rcases h3bigk with h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c | h6480c
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h3, h6388, h6394, h6396, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6445_1, p6480_1]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h3, hlam, p6480_1]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          rcases p6480_3 (m.d 0 3) (by simp) with h6484 | h6484
                                          · rcases p6480_3 (m.d 1 3) (by simp) with h6485 | h6485
                                            · linarith only [h1, h6485, hlam]
                                            · linarith only [h6391, h6485, hlam]
                                          · linarith only [h6484, hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          rcases p6480_3 (m.d 0 3) (by simp) with h6489 | h6489
                                          · rcases p6480_3 (m.d 1 3) (by simp) with h6490 | h6490
                                            · linarith only [h1, h6490, hlam]
                                            · linarith only [h6392, h6490, hlam]
                                          · linarith only [h6489, hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h1, hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6388, hlam, p6480_1]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          rcases p6480_3 (m.d 0 3) (by simp) with h6497 | h6497
                                          · rcases p6480_3 (m.d 1 3) (by simp) with h6498 | h6498
                                            · rcases p6480_3 (m.d 2 3) (by simp) with h6499 | h6499
                                              · rcases p6480_3 (m.d 3 4) (by simp) with h6500 | h6500
                                                · linarith only [h6500, hlam, p6480_0]
                                                · rcases p6480_3 (m.d 3 5) (by simp) with h6502 | h6502
                                                  · linarith only [h6392, h6502, hlam]
                                                  · linarith only [h6443, h6502, hlam]
                                              · linarith only [h6394, h6499, hlam]
                                            · linarith only [h6498, hlam, p6480_0]
                                          · linarith only [h6385, h6497, hlam]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          rcases p6480_3 (m.d 0 3) (by simp) with h6508 | h6508
                                          · rcases p6480_3 (m.d 1 3) (by simp) with h6509 | h6509
                                            · rcases p6480_3 (m.d 2 3) (by simp) with h6510 | h6510
                                              · rcases p6480_3 (m.d 3 4) (by simp) with h6511 | h6511
                                                · linarith only [h6391, h6511, hlam]
                                                · rcases p6480_3 (m.d 3 5) (by simp) with h6513 | h6513
                                                  · linarith only [h6513, hlam, p6480_0]
                                                  · rcases h5bigk with h6515c | h6515c | h6515c | h6515c | h6515c | h6515c | h6515c | h6515c | h6515c | h6515c | h6515c | h6515c | h6515c | h6515c | h6515c | h6515c | h6515c | h6515c | h6515c | h6515c | h6515c | h6515c | h6515c | h6515c | h6515c
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [hlam, p6515_0]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h6393, h6394, h6396, hc05, hc34, hlam, hphi, ht0b, ht45, ht5b, p6515_1]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h3, h6384, h6394, h6396, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6515_1]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h3, h6384, h6443, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6515_1]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h3, h6383, h6387, h6394, h6396, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6515_1]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h2, hlam, p6515_0]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [hlam, p6515_0]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h2, h6394, h6396, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6515_1]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h0, h6390, h6443, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6515_1]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h2, h3, h6383, h6387, h6394, h6396, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6515_1]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h6384, hlam, p6515_1]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h6390, hlam, p6515_1]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [hlam, p6515_0]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h3, h6384, h6443, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6515_1]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h6396, hlam, p6515_1]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h6386, hlam, p6515_0]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h6392, hlam, p6515_0]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h6395, hlam, p6515_0]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [hlam, p6515_0]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h6443, hlam, p6515_1]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h6387, hlam, p6515_0]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h6393, hlam, p6515_0]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h3, h6383, h6387, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p6515_1]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [h3, h6383, h6387, h6443, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6515_1]
                                                    · have p6515_0 := h6515c.1
                                                      have p6515_1 := h6515c.2.1
                                                      have p6515_2 := h6515c.2.2.1
                                                      have p6515_3 := h6515c.2.2.2
                                                      linarith only [hlam, p6515_0]
                                              · linarith only [h6395, h6510, hlam]
                                            · linarith only [h6509, hlam, p6480_0]
                                          · linarith only [h6386, h6508, hlam]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [hc23, hlam, hphi, ht01, ht12, p6480_1, u0ehi2]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6388, h6395, h6443, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6445_1, p6480_1]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h0, h3, h6395, h6443, hlam, p6445_1, p6480_2]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h0, h3, h6395, hlam, p6445_1, p6480_2]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6385, hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6391, hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6394, hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6443, hlam, p6480_1]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6386, hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6392, hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h6395, hlam, p6480_0]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [h0, h6395, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p6445_1, p6480_1]
                                        · have p6480_0 := h6480c.1
                                          have p6480_1 := h6480c.2.1
                                          have p6480_2 := h6480c.2.2.1
                                          have p6480_3 := h6480c.2.2.2
                                          linarith only [hlam, p6480_0]
                                  · linarith only [h6395, h6475, hlam]
                                · linarith only [h6474, hlam, p6445_0]
                              · linarith only [h6384, h6473, hlam]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              linarith only [hc23, hlam, hphi, ht01, ht12, p6445_1, u0ehi1]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              rcases p6445_3 (m.d 0 2) (by simp) with h6563 | h6563
                              · linarith only [h3, h6563, hlam]
                              · linarith only [h0, h6563, hlam]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              linarith only [hlam, p6445_0]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              linarith only [h3, h6383, h6387, h6396, hlam, p6445_2]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              rcases p6445_3 (m.d 0 2) (by simp) with h6568 | h6568
                              · linarith only [h3, h6568, hlam]
                              · linarith only [h6384, h6568, hlam]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              linarith only [h6383, hlam, p6445_0]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              linarith only [h6390, h6393, h6396, hlam, p6445_1]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              linarith only [h6394, hlam, p6445_1]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              linarith only [hlam, p6445_0]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              linarith only [h6396, hlam, p6445_1]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              linarith only [h6384, hlam, p6445_0]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              linarith only [h6390, hlam, p6445_0]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              linarith only [h6395, hlam, p6445_1]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              linarith only [h3, h6384, h6394, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6445_1]
                            · have p6445_0 := h6445c.1
                              have p6445_1 := h6445c.2.1
                              have p6445_2 := h6445c.2.2.1
                              have p6445_3 := h6445c.2.2.2
                              linarith only [hlam, p6445_0]
                      · linarith only [h3, h6395, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · linarith only [h3, h6394, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6583 | h6583
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6584 | h6584
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6585 | h6585
                        · linarith only [h3, h6383, h6391, h6393, h6585, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6587 | h6587
                          · linarith only [h6391, h6393, h6587, hlam]
                          · rcases h2bigk with h6589c | h6589c | h6589c | h6589c | h6589c | h6589c | h6589c | h6589c | h6589c | h6589c | h6589c | h6589c | h6589c | h6589c | h6589c | h6589c | h6589c | h6589c | h6589c | h6589c | h6589c | h6589c | h6589c | h6589c | h6589c
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              linarith only [hlam, p6589_0]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              linarith only [h3, hc12, hc23, hlam, hphi, p6589_1]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              linarith only [h3, hlam, p6589_0]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              rcases p6589_3 (m.d 0 2) (by simp) with h6593 | h6593
                              · rcases p6589_3 (m.d 1 2) (by simp) with h6594 | h6594
                                · linarith only [h0, h6594, hlam]
                                · linarith only [h6390, h6585, h6594, hlam]
                              · linarith only [h6593, hlam, p6589_0]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              rcases p6589_3 (m.d 0 2) (by simp) with h6598 | h6598
                              · rcases p6589_3 (m.d 1 2) (by simp) with h6599 | h6599
                                · linarith only [h0, h6599, hlam]
                                · linarith only [h6390, h6599, hlam]
                              · linarith only [h6598, hlam, p6589_0]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              linarith only [h0, hlam, p6589_0]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              linarith only [hlam, p6589_0]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              linarith only [h6388, hlam, p6589_0]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              rcases p6589_3 (m.d 0 2) (by simp) with h6606 | h6606
                              · rcases p6589_3 (m.d 1 2) (by simp) with h6607 | h6607
                                · rcases p6589_3 (m.d 2 3) (by simp) with h6608 | h6608
                                  · rcases p6589_3 (m.d 2 4) (by simp) with h6609 | h6609
                                    · linarith only [h6609, hlam, p6589_0]
                                    · rcases p6589_3 (m.d 2 5) (by simp) with h6611 | h6611
                                      · linarith only [h6390, h6611, hlam]
                                      · linarith only [h6585, h6611, hlam]
                                  · linarith only [h6583, h6608, hlam]
                                · linarith only [h6607, hlam, p6589_0]
                              · linarith only [h6383, h6606, hlam]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              rcases p6589_3 (m.d 0 2) (by simp) with h6617 | h6617
                              · rcases p6589_3 (m.d 1 2) (by simp) with h6618 | h6618
                                · rcases p6589_3 (m.d 2 3) (by simp) with h6619 | h6619
                                  · rcases p6589_3 (m.d 2 4) (by simp) with h6620 | h6620
                                    · linarith only [h6585, h6620, hlam, p6589_1]
                                    · rcases p6589_3 (m.d 2 5) (by simp) with h6622 | h6622
                                      · linarith only [h6622, hlam, p6589_0]
                                      · rcases h3bigk with h6624c | h6624c | h6624c | h6624c | h6624c | h6624c | h6624c | h6624c | h6624c | h6624c | h6624c | h6624c | h6624c | h6624c | h6624c | h6624c | h6624c | h6624c | h6624c | h6624c | h6624c | h6624c | h6624c | h6624c | h6624c
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [hlam, p6624_0]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [h6388, h6583, h6585, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p6589_1, p6624_1]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [h3, hlam, p6624_1]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          rcases p6624_3 (m.d 0 3) (by simp) with h6628 | h6628
                                          · rcases p6624_3 (m.d 1 3) (by simp) with h6629 | h6629
                                            · linarith only [h1, h6629, hlam]
                                            · linarith only [h6391, h6629, hlam]
                                          · linarith only [h6628, hlam, p6624_0]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          rcases p6624_3 (m.d 0 3) (by simp) with h6633 | h6633
                                          · rcases p6624_3 (m.d 1 3) (by simp) with h6634 | h6634
                                            · linarith only [h1, h6634, hlam]
                                            · linarith only [h6392, h6634, hlam]
                                          · linarith only [h6633, hlam, p6624_0]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [h1, hlam, p6624_0]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [hlam, p6624_0]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [h6388, hlam, p6624_1]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          rcases p6624_3 (m.d 0 3) (by simp) with h6641 | h6641
                                          · rcases p6624_3 (m.d 1 3) (by simp) with h6642 | h6642
                                            · rcases p6624_3 (m.d 2 3) (by simp) with h6643 | h6643
                                              · rcases p6624_3 (m.d 3 4) (by simp) with h6644 | h6644
                                                · linarith only [h6644, hlam, p6624_0]
                                                · rcases p6624_3 (m.d 3 5) (by simp) with h6646 | h6646
                                                  · linarith only [h6392, h6646, hlam]
                                                  · linarith only [h6587, h6646, hlam]
                                              · linarith only [h6583, h6643, hlam]
                                            · linarith only [h6642, hlam, p6624_0]
                                          · linarith only [h6385, h6641, hlam]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          rcases p6624_3 (m.d 0 3) (by simp) with h6652 | h6652
                                          · rcases p6624_3 (m.d 1 3) (by simp) with h6653 | h6653
                                            · rcases p6624_3 (m.d 2 3) (by simp) with h6654 | h6654
                                              · rcases p6624_3 (m.d 3 4) (by simp) with h6655 | h6655
                                                · linarith only [h6391, h6655, hlam]
                                                · rcases p6624_3 (m.d 3 5) (by simp) with h6657 | h6657
                                                  · linarith only [h6657, hlam, p6624_0]
                                                  · rcases h5bigk with h6659c | h6659c | h6659c | h6659c | h6659c | h6659c | h6659c | h6659c | h6659c | h6659c | h6659c | h6659c | h6659c | h6659c | h6659c | h6659c | h6659c | h6659c | h6659c | h6659c | h6659c | h6659c | h6659c | h6659c | h6659c
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [hlam, p6659_0]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h3, h6384, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6659_1]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h3, h6384, h6583, h6585, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6659_1]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h3, h6384, h6587, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6659_1]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h3, h6383, h6387, h6391, h6393, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6659_1]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h2, hlam, p6659_0]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [hlam, p6659_0]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h2, h6583, h6585, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6659_1]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h0, h6390, h6587, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6659_1]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h6393, hlam, p6659_1]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h6384, hlam, p6659_1]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h6390, hlam, p6659_1]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [hlam, p6659_0]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h3, h6384, h6587, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6659_1]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h6585, hlam, p6659_1]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h6386, hlam, p6659_0]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h6392, hlam, p6659_0]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h6584, hlam, p6659_0]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [hlam, p6659_0]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h6587, hlam, p6659_1]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h6387, hlam, p6659_0]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h3, h6383, h6387, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p6659_1]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h3, h6383, h6387, h6584, h6587, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6659_1]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [h3, h6383, h6387, h6587, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6659_1]
                                                    · have p6659_0 := h6659c.1
                                                      have p6659_1 := h6659c.2.1
                                                      have p6659_2 := h6659c.2.2.1
                                                      have p6659_3 := h6659c.2.2.2
                                                      linarith only [hlam, p6659_0]
                                              · linarith only [h6584, h6654, hlam]
                                            · linarith only [h6653, hlam, p6624_0]
                                          · linarith only [h6386, h6652, hlam]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [hc23, hlam, hphi, ht01, ht12, p6624_1, u0ehi2]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [h6388, h6584, h6587, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6589_1, p6624_1]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [hlam, p6624_0]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [h0, h3, h6584, h6587, hlam, p6589_1, p6624_2]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [h0, h3, h6584, hlam, p6589_1, p6624_2]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [h6385, hlam, p6624_0]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [h6391, hlam, p6624_0]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [h6583, hlam, p6624_0]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [hlam, p6624_0]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [h6587, hlam, p6624_1]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [h6386, hlam, p6624_0]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [h6392, hlam, p6624_0]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [h6584, hlam, p6624_0]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [h0, h6584, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p6589_1, p6624_1]
                                        · have p6624_0 := h6624c.1
                                          have p6624_1 := h6624c.2.1
                                          have p6624_2 := h6624c.2.2.1
                                          have p6624_3 := h6624c.2.2.2
                                          linarith only [hlam, p6624_0]
                                  · linarith only [h6584, h6619, hlam]
                                · linarith only [h6618, hlam, p6589_0]
                              · linarith only [h6384, h6617, hlam]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              linarith only [hc23, hlam, hphi, ht01, ht12, p6589_1, u0ehi1]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              rcases p6589_3 (m.d 0 2) (by simp) with h6707 | h6707
                              · linarith only [h3, h6707, hlam]
                              · linarith only [h0, h6707, hlam]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              linarith only [hlam, p6589_0]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              linarith only [h3, h6383, h6387, h6585, hlam, p6589_2]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              rcases p6589_3 (m.d 0 2) (by simp) with h6712 | h6712
                              · linarith only [h3, h6712, hlam]
                              · linarith only [h6384, h6712, hlam]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              linarith only [h6383, hlam, p6589_0]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              linarith only [h6383, h6387, h6585, hc02, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p6589_1]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              linarith only [h6583, hlam, p6589_1]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              linarith only [hlam, p6589_0]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              linarith only [h6585, hlam, p6589_1]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              linarith only [h6384, hlam, p6589_0]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              linarith only [h6390, hlam, p6589_0]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              linarith only [h6584, hlam, p6589_1]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              linarith only [h0, h6390, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p6589_1]
                            · have p6589_0 := h6589c.1
                              have p6589_1 := h6589c.2.1
                              have p6589_2 := h6589c.2.2.1
                              have p6589_3 := h6589c.2.2.2
                              linarith only [hlam, p6589_0]
                      · linarith only [h3, h6383, h6387, h6393, h6584, hc14, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h3, h6383, h6387, h6391, h6393, h6583, hlam]
                · linarith only [h6388, h6390, h6392, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6728 | h6728
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6729 | h6729
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6730 | h6730
                    · linarith only [h3, h6383, h6388, h6391, h6730, hc12, hc23, hlam, hphi]
                    · linarith only [h3, h6730, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                  · linarith only [h3, h6383, h6387, h6388, h6390, h6391, h6729, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b]
                · linarith only [h6388, h6390, h6728, hlam]
            · linarith only [h3, h6384, h6390, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6736 | h6736
          · linarith only [h3, h6736, hc12, hlam, hphi, ht01, u0ehi1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6738 | h6738
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6739 | h6739
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6740 | h6740
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6741 | h6741
                  · linarith only [h6387, h6739, h6741, hc13, hlam, hphi, ht01, u0ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6743 | h6743
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6744 | h6744
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6745 | h6745
                        · linarith only [h6387, h6745, hc24, hlam, hphi, ht01, ht12, u0ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6747 | h6747
                          · linarith only [h6387, h6738, h6743, h6745, h6747, hc12, hlam, hphi, ht01, u0ehi3]
                          · rcases h2bigk with h6749c | h6749c | h6749c | h6749c | h6749c | h6749c | h6749c | h6749c | h6749c | h6749c | h6749c | h6749c | h6749c | h6749c | h6749c | h6749c | h6749c | h6749c | h6749c | h6749c | h6749c | h6749c | h6749c | h6749c | h6749c
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              linarith only [hlam, p6749_0]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              linarith only [h3, hc12, hc23, hlam, hphi, p6749_1]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              linarith only [h3, hlam, p6749_0]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              rcases p6749_3 (m.d 0 2) (by simp) with h6753 | h6753
                              · rcases p6749_3 (m.d 1 2) (by simp) with h6754 | h6754
                                · linarith only [h0, h6754, hlam]
                                · linarith only [h6738, h6745, h6754, hlam]
                              · linarith only [h6753, hlam, p6749_0]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              rcases p6749_3 (m.d 0 2) (by simp) with h6758 | h6758
                              · rcases p6749_3 (m.d 1 2) (by simp) with h6759 | h6759
                                · linarith only [h0, h6759, hlam]
                                · linarith only [h6738, h6759, hlam]
                              · linarith only [h6758, hlam, p6749_0]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              linarith only [h0, hlam, p6749_0]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              linarith only [hlam, p6749_0]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              linarith only [h6736, hlam, p6749_0]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              rcases p6749_3 (m.d 0 2) (by simp) with h6766 | h6766
                              · rcases p6749_3 (m.d 1 2) (by simp) with h6767 | h6767
                                · rcases p6749_3 (m.d 2 3) (by simp) with h6768 | h6768
                                  · rcases p6749_3 (m.d 2 4) (by simp) with h6769 | h6769
                                    · linarith only [h6769, hlam, p6749_0]
                                    · rcases p6749_3 (m.d 2 5) (by simp) with h6771 | h6771
                                      · linarith only [h6738, h6771, hlam]
                                      · linarith only [h6745, h6771, hlam]
                                  · linarith only [h6743, h6768, hlam]
                                · linarith only [h6767, hlam, p6749_0]
                              · linarith only [h6383, h6766, hlam]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              rcases p6749_3 (m.d 0 2) (by simp) with h6777 | h6777
                              · rcases p6749_3 (m.d 1 2) (by simp) with h6778 | h6778
                                · rcases p6749_3 (m.d 2 3) (by simp) with h6779 | h6779
                                  · rcases p6749_3 (m.d 2 4) (by simp) with h6780 | h6780
                                    · linarith only [h6745, h6780, hlam, p6749_1]
                                    · rcases p6749_3 (m.d 2 5) (by simp) with h6782 | h6782
                                      · linarith only [h6782, hlam, p6749_0]
                                      · rcases h3bigk with h6784c | h6784c | h6784c | h6784c | h6784c | h6784c | h6784c | h6784c | h6784c | h6784c | h6784c | h6784c | h6784c | h6784c | h6784c | h6784c | h6784c | h6784c | h6784c | h6784c | h6784c | h6784c | h6784c | h6784c | h6784c
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [hlam, p6784_0]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [h3, h6736, h6743, h6745, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6749_1, p6784_1]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [h3, hlam, p6784_1]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          rcases p6784_3 (m.d 0 3) (by simp) with h6788 | h6788
                                          · rcases p6784_3 (m.d 1 3) (by simp) with h6789 | h6789
                                            · linarith only [h1, h6789, hlam]
                                            · linarith only [h6739, h6789, hlam]
                                          · linarith only [h6788, hlam, p6784_0]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          rcases p6784_3 (m.d 0 3) (by simp) with h6793 | h6793
                                          · rcases p6784_3 (m.d 1 3) (by simp) with h6794 | h6794
                                            · linarith only [h1, h6794, hlam]
                                            · linarith only [h6740, h6794, hlam]
                                          · linarith only [h6793, hlam, p6784_0]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [h1, hlam, p6784_0]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [hlam, p6784_0]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [h6736, hlam, p6784_1]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          rcases p6784_3 (m.d 0 3) (by simp) with h6801 | h6801
                                          · rcases p6784_3 (m.d 1 3) (by simp) with h6802 | h6802
                                            · rcases p6784_3 (m.d 2 3) (by simp) with h6803 | h6803
                                              · rcases p6784_3 (m.d 3 4) (by simp) with h6804 | h6804
                                                · linarith only [h6804, hlam, p6784_0]
                                                · rcases p6784_3 (m.d 3 5) (by simp) with h6806 | h6806
                                                  · linarith only [h6740, h6806, hlam]
                                                  · linarith only [h6747, h6806, hlam]
                                              · linarith only [h6743, h6803, hlam]
                                            · linarith only [h6802, hlam, p6784_0]
                                          · linarith only [h6385, h6801, hlam]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          rcases p6784_3 (m.d 0 3) (by simp) with h6812 | h6812
                                          · rcases p6784_3 (m.d 1 3) (by simp) with h6813 | h6813
                                            · rcases p6784_3 (m.d 2 3) (by simp) with h6814 | h6814
                                              · rcases p6784_3 (m.d 3 4) (by simp) with h6815 | h6815
                                                · linarith only [h6739, h6815, hlam]
                                                · rcases p6784_3 (m.d 3 5) (by simp) with h6817 | h6817
                                                  · linarith only [h6817, hlam, p6784_0]
                                                  · rcases h5bigk with h6819c | h6819c | h6819c | h6819c | h6819c | h6819c | h6819c | h6819c | h6819c | h6819c | h6819c | h6819c | h6819c | h6819c | h6819c | h6819c | h6819c | h6819c | h6819c | h6819c | h6819c | h6819c | h6819c | h6819c | h6819c
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [hlam, p6819_0]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [h3, h6384, h6738, h6743, h6745, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6819_1]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [h3, h6384, h6743, h6745, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6819_1]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [h3, h6384, h6747, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6819_1]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [h6387, hlam, p6819_1]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [h2, hlam, p6819_0]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [hlam, p6819_0]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [h2, h6743, h6745, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6819_1]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [h0, h6738, h6747, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p6819_1]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [h6741, hlam, p6819_1]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [h6384, hlam, p6819_1]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [h6738, hlam, p6819_1]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [hlam, p6819_0]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [h3, h6384, h6747, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6819_1]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [h6745, hlam, p6819_1]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [h6386, hlam, p6819_0]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [h6740, hlam, p6819_0]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [h6744, hlam, p6819_0]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [hlam, p6819_0]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [h6747, hlam, p6819_1]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [hc45, hlam, hphi, ht01, ht12, ht23, ht34, p6819_1, u0ehi4]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [h6740, h6747, hc34, hc45, hlam, hphi, p6819_1]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [h6744, h6747, hc34, hc45, hlam, hphi, p6819_1]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [h6747, hc34, hc45, hlam, hphi, p6819_1]
                                                    · have p6819_0 := h6819c.1
                                                      have p6819_1 := h6819c.2.1
                                                      have p6819_2 := h6819c.2.2.1
                                                      have p6819_3 := h6819c.2.2.2
                                                      linarith only [hlam, p6819_0]
                                              · linarith only [h6744, h6814, hlam]
                                            · linarith only [h6813, hlam, p6784_0]
                                          · linarith only [h6386, h6812, hlam]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [hc23, hlam, hphi, ht01, ht12, p6784_1, u0ehi2]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [h6736, h6744, h6747, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p6749_1, p6784_1]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [hlam, p6784_0]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [h0, h3, h6744, h6747, hlam, p6749_1, p6784_2]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [h0, h3, h6744, hlam, p6749_1, p6784_2]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [h6385, hlam, p6784_0]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [h6739, hlam, p6784_0]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [h6743, hlam, p6784_0]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [hlam, p6784_0]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [h6747, hlam, p6784_1]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [h6386, hlam, p6784_0]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [h6740, hlam, p6784_0]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [h6744, hlam, p6784_0]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [h0, h6744, hc02, hc34, hlam, hphi, ht0b, ht45, ht5b, p6749_1, p6784_1]
                                        · have p6784_0 := h6784c.1
                                          have p6784_1 := h6784c.2.1
                                          have p6784_2 := h6784c.2.2.1
                                          have p6784_3 := h6784c.2.2.2
                                          linarith only [hlam, p6784_0]
                                  · linarith only [h6744, h6779, hlam]
                                · linarith only [h6778, hlam, p6749_0]
                              · linarith only [h6384, h6777, hlam]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              linarith only [hc23, hlam, hphi, ht01, ht12, p6749_1, u0ehi1]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              rcases p6749_3 (m.d 0 2) (by simp) with h6867 | h6867
                              · linarith only [h3, h6867, hlam]
                              · linarith only [h0, h6867, hlam]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              linarith only [hlam, p6749_0]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              rcases p6749_3 (m.d 0 2) (by simp) with h6871 | h6871
                              · linarith only [h3, h6871, hlam]
                              · linarith only [h6383, h6871, hlam]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              rcases p6749_3 (m.d 0 2) (by simp) with h6874 | h6874
                              · linarith only [h3, h6874, hlam]
                              · linarith only [h6384, h6874, hlam]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              linarith only [h6383, hlam, p6749_0]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              linarith only [h6738, h6745, hlam, p6749_1]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              linarith only [h6743, hlam, p6749_1]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              linarith only [hlam, p6749_0]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              linarith only [h6745, hlam, p6749_1]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              linarith only [h6384, hlam, p6749_0]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              linarith only [h6738, hlam, p6749_0]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              linarith only [h6744, hlam, p6749_1]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              linarith only [h0, h6738, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p6749_1]
                            · have p6749_0 := h6749c.1
                              have p6749_1 := h6749c.2.1
                              have p6749_2 := h6749c.2.2.1
                              have p6749_3 := h6749c.2.2.2
                              linarith only [hlam, p6749_0]
                      · linarith only [h3, h6744, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                    · linarith only [h3, h6384, h6387, h6739, h6743, hc14, hlam, hphi, ht01, u0ehi3]
                · linarith only [h6736, h6738, h6740, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6890 | h6890
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6891 | h6891
                  · linarith only [h6385, h6387, h6736, h6738, h6739, h6891, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h6736, h6738, h6739, h6891, hlam]
                · linarith only [h6736, h6738, h6890, hlam]
            · linarith only [h3, h6384, h6738, hc12, hc23, hlam, hphi]
      · linarith only [h3, h6384, h6386, hlam]
    · linarith only [h3, h6383, h6385, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h6898 | h6898
    · rcases m.htr 0 3 5 (by decide) (by decide) with h6899 | h6899
      · rcases m.htr 0 4 5 (by decide) (by decide) with h6900 | h6900
        · linarith only [h6383, h6384, h6900, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h6902 | h6902
          · linarith only [h0, h3, h6902, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6904 | h6904
            · linarith only [h0, h6384, h6904, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h6906 | h6906
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6907 | h6907
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6908 | h6908
                  · linarith only [h6900, h6908, hc14, hlam, hphi, ht01, u0ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6910 | h6910
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6911 | h6911
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6912 | h6912
                        · linarith only [h6383, h6900, h6912, hc02, hlam, hphi, u0ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6914 | h6914
                          · linarith only [h6383, h6384, h6910, h6912, h6914, hlam]
                          · rcases h2bigk with h6916c | h6916c | h6916c | h6916c | h6916c | h6916c | h6916c | h6916c | h6916c | h6916c | h6916c | h6916c | h6916c | h6916c | h6916c | h6916c | h6916c | h6916c | h6916c | h6916c | h6916c | h6916c | h6916c | h6916c | h6916c
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [hlam, p6916_0]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [h6384, h6912, hc12, hc45, hlam, hphi, ht23, ht34, p6916_1]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [h3, hlam, p6916_0]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [h6384, h6912, hc24, hc45, hlam, hphi, p6916_1]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [h6384, hlam, p6916_0]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [h0, hlam, p6916_0]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [hlam, p6916_0]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [h6902, hlam, p6916_0]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [h0, h6384, h6910, h6912, hc34, hc45, hlam, hphi, p6916_1]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [h6904, hlam, p6916_0]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [hc23, hlam, hphi, ht01, ht12, p6916_1, u0ehi1]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              rcases p6916_3 (m.d 0 2) (by simp) with h6928 | h6928
                              · linarith only [h3, h6928, hlam]
                              · linarith only [h0, h6928, hlam]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [hlam, p6916_0]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              rcases p6916_3 (m.d 0 2) (by simp) with h6932 | h6932
                              · linarith only [h3, h6932, hlam]
                              · linarith only [h6383, h6932, hlam]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [h6383, h6384, hc23, hlam, hphi, ht01, ht12, p6916_1, u0ehi3]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [h6383, hlam, p6916_0]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [h6383, h6384, h6912, hc12, hc45, hlam, hphi, ht23, ht34, p6916_1]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [h6910, hlam, p6916_1]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [hlam, p6916_0]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [h6912, hlam, p6916_1]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [h6383, h6912, hc45, hlam, hphi, ht01, ht12, ht23, ht34, p6916_1, u0ehi3]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              rcases p6916_3 (m.d 0 2) (by simp) with h6942 | h6942
                              · linarith only [h6384, h6942, hlam]
                              · linarith only [h0, h6942, hlam]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [h6911, hlam, p6916_1]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              rcases p6916_3 (m.d 0 2) (by simp) with h6946 | h6946
                              · linarith only [h6384, h6946, hlam]
                              · linarith only [h6383, h6946, hlam]
                            · have p6916_0 := h6916c.1
                              have p6916_1 := h6916c.2.1
                              have p6916_2 := h6916c.2.2.1
                              have p6916_3 := h6916c.2.2.2
                              linarith only [hlam, p6916_0]
                      · linarith only [h1, h3, h6383, h6907, h6911, hc01, hlam, hphi, u0ehi3]
                    · linarith only [h3, h6383, h6910, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6952 | h6952
                  · linarith only [h6900, h6952, hc14, hlam, hphi, ht01, u0ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h6954 | h6954
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h6955 | h6955
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h6956 | h6956
                        · linarith only [h6383, h6900, h6956, hc02, hlam, hphi, u0ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h6958 | h6958
                          · linarith only [h3, h6384, h6899, h6906, h6907, h6956, h6958, hc02, hc23, hlam, hphi]
                          · rcases h2bigk with h6960c | h6960c | h6960c | h6960c | h6960c | h6960c | h6960c | h6960c | h6960c | h6960c | h6960c | h6960c | h6960c | h6960c | h6960c | h6960c | h6960c | h6960c | h6960c | h6960c | h6960c | h6960c | h6960c | h6960c | h6960c
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [hlam, p6960_0]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [h6384, h6956, hc12, hc45, hlam, hphi, ht23, ht34, p6960_1]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [h3, hlam, p6960_0]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [h6384, h6956, hc24, hc45, hlam, hphi, p6960_1]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [h6384, hlam, p6960_0]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [h0, hlam, p6960_0]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [hlam, p6960_0]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [h6902, hlam, p6960_0]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [h0, h6384, h6954, h6956, hc34, hc45, hlam, hphi, p6960_1]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [h6904, hlam, p6960_0]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [hc23, hlam, hphi, ht01, ht12, p6960_1, u0ehi1]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              rcases p6960_3 (m.d 0 2) (by simp) with h6972 | h6972
                              · linarith only [h3, h6972, hlam]
                              · linarith only [h0, h6972, hlam]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [hlam, p6960_0]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              rcases p6960_3 (m.d 0 2) (by simp) with h6976 | h6976
                              · linarith only [h3, h6976, hlam]
                              · linarith only [h6383, h6976, hlam]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [h6383, h6384, hc23, hlam, hphi, ht01, ht12, p6960_1, u0ehi3]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [h6383, hlam, p6960_0]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [h6383, h6384, hc12, hc25, hlam, hphi, p6960_1]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [h6954, hlam, p6960_1]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [hlam, p6960_0]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [h6956, hlam, p6960_1]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht12, p6960_1, u0ehi1]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              rcases p6960_3 (m.d 0 2) (by simp) with h6986 | h6986
                              · linarith only [h6384, h6986, hlam]
                              · linarith only [h0, h6986, hlam]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [h6955, hlam, p6960_1]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              rcases p6960_3 (m.d 0 2) (by simp) with h6990 | h6990
                              · linarith only [h6384, h6990, hlam]
                              · linarith only [h6383, h6990, hlam]
                            · have p6960_0 := h6960c.1
                              have p6960_1 := h6960c.2.1
                              have p6960_2 := h6960c.2.2.1
                              have p6960_3 := h6960c.2.2.2
                              linarith only [hlam, p6960_0]
                      · linarith only [h3, h6899, h6955, hlam]
                    · linarith only [h3, h6899, h6907, h6954, hc13, hc34, hlam, hphi]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h6996 | h6996
                · rcases m.htr 1 4 5 (by decide) (by decide) with h6997 | h6997
                  · linarith only [h6898, h6900, h6906, h6996, h6997, hc14, hc35, hlam, hphi, ht01, ht0b, ht5b]
                  · linarith only [h6906, h6996, h6997, hlam]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7000 | h7000
                  · linarith only [h6900, h7000, hc14, hlam, hphi, ht01, u0ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7002 | h7002
                    · linarith only [h3, h6383, h6902, h6906, h7002, hc12, hc23, hlam, hphi]
                    · linarith only [h3, h7002, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
      · rcases m.htr 0 4 5 (by decide) (by decide) with h7005 | h7005
        · linarith only [h3, h6383, h6899, h7005, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h7007 | h7007
          · linarith only [h3, h7007, hc12, hlam, hphi, ht01, u0ehi1]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h7009 | h7009
            · linarith only [h0, h6384, h7009, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7011 | h7011
              · rcases m.htr 1 3 5 (by decide) (by decide) with h7012 | h7012
                · linarith only [h3, h6383, h6899, h7012, hc13, hlam, hphi, ht01, u0ehi3]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h7014 | h7014
                  · linarith only [h7005, h7014, hc14, hlam, hphi, ht01, u0ehi3]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h7016 | h7016
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h7017 | h7017
                      · linarith only [h3, h6383, h6899, h7017, hc23, hlam, hphi, ht01, ht12, u0ehi3]
                      · linarith only [h3, h6383, h7017, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi3]
                    · linarith only [h3, h6383, h7016, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi3]
              · linarith only [h6898, h6899, h7011, hc13, hc35, hlam, hphi]
    · linarith only [h3, h6383, h6898, hlam]

end R2N4
