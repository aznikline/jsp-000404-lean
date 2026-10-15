import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 13584000 in
set_option maxHeartbeats 13584000 in
theorem r1l7_20_12_14_M_LI_L_I_L_I_s0_x1_x0_x0_x1_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h5410 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h5411 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h5412 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
    (h5414 : (m.d 0 2 + m.lam ≤ m.d 2 4 ∧ m.d 0 2 < m.d 0 4 ∧ m.d 0 4 < m.d 2 4))
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
  have h0elo := hb0.1
  have h0emin := hb0.2.1
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have h0 := hg0
  rcases m.htr 0 2 5 (by decide) (by decide) with h5415 | h5415
  · rcases m.htr 0 3 4 (by decide) (by decide) with h5416 | h5416
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5417 | h5417
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5418 | h5418
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5419 | h5419
          · linarith only [h0, h1, h5412, h5414, h5419, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5421 | h5421
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5422 | h5422
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5423 | h5423
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5424 | h5424
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5425 | h5425
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5426 | h5426
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5427 | h5427
                        · linarith only [h0, h1, h5419, h5421, h5427, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b]
                        · linarith only [h0, h1, h5419, h5421, h5424, h5427, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                      · linarith only [h0, h1, h5419, h5426, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h1, h5419, h5425, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5432 | h5432
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5433 | h5433
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5434 | h5434
                        · linarith only [h0, h1, h5419, h5421, h5424, h5434, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5436 | h5436
                          · linarith only [h5421, h5424, h5432, h5436, hlam]
                          · rcases h0bigk with h5438c | h5438c | h5438c | h5438c | h5438c | h5438c | h5438c | h5438c | h5438c | h5438c | h5438c | h5438c | h5438c | h5438c | h5438c | h5438c | h5438c | h5438c | h5438c | h5438c | h5438c | h5438c | h5438c | h5438c | h5438c
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [hlam, p5438_0]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h1, h5419, hc02, hc23, hlam, hphi, p5438_1]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h1, hlam, p5438_0]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h1, h5418, h5419, h5421, h5424, h5432, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5438_1]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h1, h5418, h5419, h5421, h5424, h5432, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5438_1]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h0, hlam, p5438_0]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [hlam, p5438_0]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h5412, hlam, p5438_0]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h5418, h5421, h5424, h5432, hc34, hlam, hphi, ht0b, ht45, ht5b, p5438_1, u0elo1]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h0, h1, h5418, h5419, h5421, h5424, h5432, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5438_1]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5438_1, u0elo2]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h5414, h5432, hc34, hlam, hphi, ht0b, ht45, ht5b, p5438_1, u0elo2]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [hlam, p5438_0]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h5418, h5421, h5424, h5432, hc34, hlam, hphi, ht0b, ht45, ht5b, p5438_1, u0elo2]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h5418, h5421, h5424, h5432, hc34, hlam, hphi, ht0b, ht45, ht5b, p5438_1, u0elo2]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h5410, hlam, p5438_0]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h5414, hlam, p5438_0]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h5416, hlam, p5438_0]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [hlam, p5438_0]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h0, h1, h5414, h5418, h5419, h5421, h5424, h5432, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5438_1]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h5411, hlam, p5438_0]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h5415, hlam, p5438_1]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h5417, hlam, p5438_0]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [h5418, hlam, p5438_1]
                            · have p5438_0 := h5438c.1
                              have p5438_1 := h5438c.2.1
                              have p5438_2 := h5438c.2.2.1
                              have p5438_3 := h5438c.2.2.2
                              linarith only [hlam, p5438_0]
                      · linarith only [h0, h1, h5419, h5421, h5432, h5433, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                    · linarith only [h0, h1, h5414, h5418, h5419, h5424, h5432, hc14, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h1, h5416, h5423, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
              · linarith only [h5415, h5421, h5422, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · linarith only [h0, h1, h5414, h5419, h5421, hc12, hc23, hlam, hphi]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5469 | h5469
          · linarith only [h0, h5412, h5469, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5471 | h5471
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5472 | h5472
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5473 | h5473
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5474 | h5474
                  · linarith only [h5410, h5418, h5474, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5476 | h5476
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5477 | h5477
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5478 | h5478
                        · linarith only [h5410, h5418, h5471, h5478, hlam]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5480 | h5480
                          · linarith only [h5410, h5418, h5471, h5476, h5480, hlam]
                          · rcases h0bigk with h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c | h5482c
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              linarith only [hlam, p5482_0]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              linarith only [h0, h1, h5469, h5472, h5476, h5478, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5482_1]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              linarith only [h1, hlam, p5482_0]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              rcases p5482_3 (m.d 0 1) (by simp) with h5486 | h5486
                              · rcases p5482_3 (m.d 0 2) (by simp) with h5487 | h5487
                                · linarith only [h0, h5487, hlam]
                                · linarith only [h5414, h5487, hlam]
                              · linarith only [h5410, h5486, hlam]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              rcases p5482_3 (m.d 0 1) (by simp) with h5491 | h5491
                              · rcases p5482_3 (m.d 0 2) (by simp) with h5492 | h5492
                                · linarith only [h0, h5492, hlam]
                                · linarith only [h5415, h5492, hlam]
                              · linarith only [h5411, h5491, hlam]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              linarith only [h0, hlam, p5482_0]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              linarith only [hlam, p5482_0]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              linarith only [h5412, hlam, p5482_0]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              rcases p5482_3 (m.d 0 1) (by simp) with h5499 | h5499
                              · rcases p5482_3 (m.d 0 2) (by simp) with h5500 | h5500
                                · rcases p5482_3 (m.d 0 3) (by simp) with h5501 | h5501
                                  · rcases p5482_3 (m.d 0 4) (by simp) with h5502 | h5502
                                    · linarith only [h5414, h5502, hlam]
                                    · rcases p5482_3 (m.d 0 5) (by simp) with h5504 | h5504
                                      · linarith only [h5415, h5504, hlam]
                                      · linarith only [h5418, h5504, hlam]
                                  · linarith only [h5416, h5501, hlam]
                                · linarith only [h5414, h5500, hlam]
                              · linarith only [h5410, h5499, hlam]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              rcases p5482_3 (m.d 0 1) (by simp) with h5510 | h5510
                              · rcases p5482_3 (m.d 0 2) (by simp) with h5511 | h5511
                                · rcases p5482_3 (m.d 0 3) (by simp) with h5512 | h5512
                                  · rcases p5482_3 (m.d 0 4) (by simp) with h5513 | h5513
                                    · linarith only [h5414, h5513, hlam]
                                    · rcases p5482_3 (m.d 0 5) (by simp) with h5515 | h5515
                                      · linarith only [h5415, h5515, hlam]
                                      · rcases h0emin with h5517 | h5517 | h5517 | h5517 | h5517
                                        · rcases h2bigk with h5518c | h5518c | h5518c | h5518c | h5518c | h5518c | h5518c | h5518c | h5518c | h5518c | h5518c | h5518c | h5518c | h5518c | h5518c | h5518c | h5518c | h5518c | h5518c | h5518c | h5518c | h5518c | h5518c | h5518c | h5518c
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [hlam, p5518_0]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [h5472, h5476, h5478, hc34, hlam, hphi, ht0b, ht45, ht5b, p5518_1, u0elo1]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [h5412, hlam, p5518_0]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            rcases p5518_3 (m.d 0 2) (by simp) with h5522 | h5522
                                            · rcases p5518_3 (m.d 1 2) (by simp) with h5523 | h5523
                                              · linarith only [h0, h5523, hlam]
                                              · linarith only [h5471, h5523, hlam]
                                            · linarith only [h5522, hlam, p5518_0]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            rcases p5518_3 (m.d 0 2) (by simp) with h5527 | h5527
                                            · rcases p5518_3 (m.d 1 2) (by simp) with h5528 | h5528
                                              · linarith only [h0, h5528, hlam]
                                              · linarith only [h5472, h5528, hlam]
                                            · linarith only [h5527, hlam, p5518_0]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [h0, hlam, p5518_0]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [hlam, p5518_0]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [h5469, hlam, p5518_0]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [h0, h1, h5469, h5476, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5518_1]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [h0, h1, h5469, h5476, h5478, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5518_1]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [h5410, h5418, h5471, h5476, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5482_1, p5518_1]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            rcases p5518_3 (m.d 0 2) (by simp) with h5538 | h5538
                                            · linarith only [h5412, h5538, hlam]
                                            · linarith only [h0, h5538, hlam]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [hlam, p5518_0]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [h0, h1, h5410, h5418, h5469, h5471, hlam, p5482_1, p5518_2]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [h0, h1, h5415, h5469, hlam, p5482_1, p5518_2]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [h5414, hlam, p5518_0]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [h5471, hlam, p5518_0]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [h5476, hlam, p5518_1]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [hlam, p5518_0]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [h5478, hlam, p5518_1]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [h5415, hlam, p5518_0]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [h5472, hlam, p5518_0]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [h5477, hlam, p5518_1]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [h0, h5411, h5472, h5476, hc34, hlam, hphi, ht0b, ht45, ht5b, p5482_1, p5518_1, u0elo0]
                                          · have p5518_0 := h5518c.1
                                            have p5518_1 := h5518c.2.1
                                            have p5518_2 := h5518c.2.2.1
                                            have p5518_3 := h5518c.2.2.2
                                            linarith only [hlam, p5518_0]
                                        · rcases h2bigk with h5554c | h5554c | h5554c | h5554c | h5554c | h5554c | h5554c | h5554c | h5554c | h5554c | h5554c | h5554c | h5554c | h5554c | h5554c | h5554c | h5554c | h5554c | h5554c | h5554c | h5554c | h5554c | h5554c | h5554c | h5554c
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [hlam, p5554_0]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [h0, h1, h5469, hc12, hc23, hlam, hphi, p5554_1]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [h5412, hlam, p5554_0]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            rcases p5554_3 (m.d 0 2) (by simp) with h5558 | h5558
                                            · rcases p5554_3 (m.d 1 2) (by simp) with h5559 | h5559
                                              · linarith only [h0, h5559, hlam]
                                              · linarith only [h5471, h5559, hlam]
                                            · linarith only [h5558, hlam, p5554_0]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            rcases p5554_3 (m.d 0 2) (by simp) with h5563 | h5563
                                            · rcases p5554_3 (m.d 1 2) (by simp) with h5564 | h5564
                                              · linarith only [h0, h5564, hlam]
                                              · linarith only [h5472, h5564, hlam]
                                            · linarith only [h5563, hlam, p5554_0]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [h0, hlam, p5554_0]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [hlam, p5554_0]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [h5469, hlam, p5554_0]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [h0, h1, h5469, h5476, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5554_1]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [h0, h1, h5469, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p5554_1]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [h5517, hc23, hlam, ht01, ht12, p5554_1]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            rcases p5554_3 (m.d 0 2) (by simp) with h5574 | h5574
                                            · linarith only [h5412, h5574, hlam]
                                            · linarith only [h0, h5574, hlam]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [hlam, p5554_0]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [h0, h1, h5410, h5418, h5469, h5471, hlam, p5482_1, p5554_2]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [h0, h1, h5415, h5469, hlam, p5482_1, p5554_2]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [h5414, hlam, p5554_0]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [h5471, hlam, p5554_0]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [h5476, hlam, p5554_1]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [hlam, p5554_0]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [h5478, hlam, p5554_1]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [h5415, hlam, p5554_0]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [h5472, hlam, p5554_0]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [h5477, hlam, p5554_1]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [h0, h5411, h5472, h5476, hc34, hlam, hphi, ht0b, ht45, ht5b, p5482_1, p5554_1, u0elo0]
                                          · have p5554_0 := h5554c.1
                                            have p5554_1 := h5554c.2.1
                                            have p5554_2 := h5554c.2.2.1
                                            have p5554_3 := h5554c.2.2.2
                                            linarith only [hlam, p5554_0]
                                        · rcases h2bigk with h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c | h5590c
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [hlam, p5590_0]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [h0, h1, h5469, hc12, hc23, hlam, hphi, p5590_1]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [h5412, hlam, p5590_0]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            rcases p5590_3 (m.d 0 2) (by simp) with h5594 | h5594
                                            · rcases p5590_3 (m.d 1 2) (by simp) with h5595 | h5595
                                              · linarith only [h0, h5595, hlam]
                                              · linarith only [h5471, h5595, hlam]
                                            · linarith only [h5594, hlam, p5590_0]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            rcases p5590_3 (m.d 0 2) (by simp) with h5599 | h5599
                                            · rcases p5590_3 (m.d 1 2) (by simp) with h5600 | h5600
                                              · linarith only [h0, h5600, hlam]
                                              · linarith only [h5472, h5600, hlam]
                                            · linarith only [h5599, hlam, p5590_0]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [h0, hlam, p5590_0]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [hlam, p5590_0]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [h5469, hlam, p5590_0]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [h0, h1, h5469, h5476, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5590_1]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [h0, h1, h5469, h5477, h5480, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5590_1]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p5482_1, p5590_1]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            rcases p5590_3 (m.d 0 2) (by simp) with h5610 | h5610
                                            · linarith only [h5412, h5610, hlam]
                                            · linarith only [h0, h5610, hlam]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [hlam, p5590_0]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [h0, h1, h5410, h5418, h5469, h5471, hlam, p5482_1, p5590_2]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [h0, h1, h5411, h5469, h5472, hlam, p5482_1, p5590_2]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [h5414, hlam, p5590_0]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [h5471, hlam, p5590_0]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [h5476, hlam, p5590_1]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [hlam, p5590_0]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [h5478, hlam, p5590_1]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [h5415, hlam, p5590_0]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [h5472, hlam, p5590_0]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [h5477, hlam, p5590_1]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [h0, h5411, h5472, h5476, hc34, hlam, hphi, ht0b, ht45, ht5b, p5482_1, p5590_1, u0elo0]
                                          · have p5590_0 := h5590c.1
                                            have p5590_1 := h5590c.2.1
                                            have p5590_2 := h5590c.2.2.1
                                            have p5590_3 := h5590c.2.2.2
                                            linarith only [hlam, p5590_0]
                                        · linarith only [h0, h1, h5418, h5469, h5517, hc23, hlam, ht01, ht12, p5482_1]
                                        · linarith only [h0, h1, h5469, h5517, hc23, hlam, ht01, ht12, p5482_1]
                                  · linarith only [h5417, h5512, hlam]
                                · linarith only [h5415, h5511, hlam]
                              · linarith only [h5411, h5510, hlam]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              linarith only [h0, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5482_1, u0elo2]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              linarith only [h5414, h5476, hc34, hlam, hphi, ht0b, ht45, ht5b, p5482_1, u0elo2]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              linarith only [hlam, p5482_0]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              rcases p5482_3 (m.d 0 1) (by simp) with h5634 | h5634
                              · linarith only [h1, h5634, hlam]
                              · linarith only [h5410, h5634, hlam]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              rcases p5482_3 (m.d 0 1) (by simp) with h5637 | h5637
                              · linarith only [h1, h5637, hlam]
                              · linarith only [h5411, h5637, hlam]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              linarith only [h5410, hlam, p5482_0]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              linarith only [h5414, hlam, p5482_0]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              linarith only [h5416, hlam, p5482_0]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              linarith only [hlam, p5482_0]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              linarith only [h5418, hlam, p5482_0]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              linarith only [h5411, hlam, p5482_0]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              linarith only [h5415, hlam, p5482_1]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              linarith only [h5417, hlam, p5482_0]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              rcases p5482_3 (m.d 0 1) (by simp) with h5648 | h5648
                              · rcases p5482_3 (m.d 0 2) (by simp) with h5649 | h5649
                                · rcases p5482_3 (m.d 0 3) (by simp) with h5650 | h5650
                                  · rcases p5482_3 (m.d 0 4) (by simp) with h5651 | h5651
                                    · linarith only [h5418, h5651, hlam]
                                    · rcases p5482_3 (m.d 0 5) (by simp) with h5653 | h5653
                                      · rcases h0emin with h5654 | h5654 | h5654 | h5654 | h5654
                                        · rcases h2bigk with h5655c | h5655c | h5655c | h5655c | h5655c | h5655c | h5655c | h5655c | h5655c | h5655c | h5655c | h5655c | h5655c | h5655c | h5655c | h5655c | h5655c | h5655c | h5655c | h5655c | h5655c | h5655c | h5655c | h5655c | h5655c
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [hlam, p5655_0]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [h0, h1, h5469, h5472, h5477, h5480, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5655_1]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [h5412, hlam, p5655_0]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            rcases p5655_3 (m.d 0 2) (by simp) with h5659 | h5659
                                            · rcases p5655_3 (m.d 1 2) (by simp) with h5660 | h5660
                                              · linarith only [h0, h5660, hlam]
                                              · linarith only [h5471, h5660, hlam]
                                            · linarith only [h5659, hlam, p5655_0]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            rcases p5655_3 (m.d 0 2) (by simp) with h5664 | h5664
                                            · rcases p5655_3 (m.d 1 2) (by simp) with h5665 | h5665
                                              · linarith only [h0, h5665, hlam]
                                              · linarith only [h5472, h5665, hlam]
                                            · linarith only [h5664, hlam, p5655_0]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [h0, hlam, p5655_0]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [hlam, p5655_0]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [h5469, hlam, p5655_0]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [h0, h1, h5469, h5476, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5655_1]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [h0, h1, h5469, h5477, h5480, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5655_1]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [h5410, h5415, h5471, h5476, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5482_1, p5655_1]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            rcases p5655_3 (m.d 0 2) (by simp) with h5675 | h5675
                                            · linarith only [h5412, h5675, hlam]
                                            · linarith only [h0, h5675, hlam]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [hlam, p5655_0]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [h0, h1, h5410, h5415, h5469, h5471, hlam, p5482_1, p5655_2]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [h0, h1, h5469, h5472, hlam, p5655_2]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [h5414, hlam, p5655_0]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [h5471, hlam, p5655_0]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [h5476, hlam, p5655_1]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [hlam, p5655_0]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [h5478, hlam, p5655_1]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [h5415, hlam, p5655_0]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [h5472, hlam, p5655_0]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [h5477, hlam, p5655_1]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [h0, h5472, h5476, hc34, hlam, hphi, ht0b, ht45, ht5b, p5655_1, u0elo0]
                                          · have p5655_0 := h5655c.1
                                            have p5655_1 := h5655c.2.1
                                            have p5655_2 := h5655c.2.2.1
                                            have p5655_3 := h5655c.2.2.2
                                            linarith only [hlam, p5655_0]
                                        · rcases h2bigk with h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c | h5691c
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [hlam, p5691_0]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [h5472, hc25, hlam, hphi, ht0b, ht5b, p5691_1, u0elo1]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [h5412, hlam, p5691_0]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            rcases p5691_3 (m.d 0 2) (by simp) with h5695 | h5695
                                            · rcases p5691_3 (m.d 1 2) (by simp) with h5696 | h5696
                                              · linarith only [h0, h5696, hlam]
                                              · linarith only [h5471, h5696, hlam]
                                            · linarith only [h5695, hlam, p5691_0]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            rcases p5691_3 (m.d 0 2) (by simp) with h5700 | h5700
                                            · rcases p5691_3 (m.d 1 2) (by simp) with h5701 | h5701
                                              · linarith only [h0, h5701, hlam]
                                              · linarith only [h5472, h5701, hlam]
                                            · linarith only [h5700, hlam, p5691_0]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [h0, hlam, p5691_0]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [hlam, p5691_0]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [h5469, hlam, p5691_0]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [h0, h1, h5469, h5476, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5691_1]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [h0, h1, h5469, h5477, h5480, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5691_1]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [h5654, hc23, hlam, ht01, ht12, p5691_1]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            rcases p5691_3 (m.d 0 2) (by simp) with h5711 | h5711
                                            · linarith only [h5412, h5711, hlam]
                                            · linarith only [h0, h5711, hlam]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [hlam, p5691_0]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [h0, h1, h5410, h5415, h5469, h5471, hlam, p5482_1, p5691_2]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [h0, h1, h5469, h5472, hlam, p5691_2]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [h5414, hlam, p5691_0]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [h5471, hlam, p5691_0]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [h5476, hlam, p5691_1]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [hlam, p5691_0]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [h5478, hlam, p5691_1]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [h5415, hlam, p5691_0]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [h5472, hlam, p5691_0]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [h5477, hlam, p5691_1]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [h0, h5472, h5476, hc34, hlam, hphi, ht0b, ht45, ht5b, p5691_1, u0elo0]
                                          · have p5691_0 := h5691c.1
                                            have p5691_1 := h5691c.2.1
                                            have p5691_2 := h5691c.2.2.1
                                            have p5691_3 := h5691c.2.2.2
                                            linarith only [hlam, p5691_0]
                                        · rcases h2bigk with h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c | h5727c
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [hlam, p5727_0]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [h5472, hc25, hlam, hphi, ht0b, ht5b, p5727_1, u0elo1]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [h5412, hlam, p5727_0]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            rcases p5727_3 (m.d 0 2) (by simp) with h5731 | h5731
                                            · rcases p5727_3 (m.d 1 2) (by simp) with h5732 | h5732
                                              · linarith only [h0, h5732, hlam]
                                              · linarith only [h5471, h5732, hlam]
                                            · linarith only [h5731, hlam, p5727_0]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            rcases p5727_3 (m.d 0 2) (by simp) with h5736 | h5736
                                            · rcases p5727_3 (m.d 1 2) (by simp) with h5737 | h5737
                                              · linarith only [h0, h5737, hlam]
                                              · linarith only [h5472, h5737, hlam]
                                            · linarith only [h5736, hlam, p5727_0]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [h0, hlam, p5727_0]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [hlam, p5727_0]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [h5469, hlam, p5727_0]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [h0, h1, h5469, h5476, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5727_1]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [h0, h1, h5469, h5477, h5480, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5727_1]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [h5410, h5415, h5471, h5476, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5482_1, p5727_1]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            rcases p5727_3 (m.d 0 2) (by simp) with h5747 | h5747
                                            · linarith only [h5412, h5747, hlam]
                                            · linarith only [h0, h5747, hlam]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [hlam, p5727_0]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [h0, h1, h5410, h5415, h5469, h5471, hlam, p5482_1, p5727_2]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [h0, h1, h5469, h5472, hlam, p5727_2]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [h5414, hlam, p5727_0]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [h5471, hlam, p5727_0]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [h5476, hlam, p5727_1]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [hlam, p5727_0]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [h5478, hlam, p5727_1]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [h5415, hlam, p5727_0]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [h5472, hlam, p5727_0]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [h5477, hlam, p5727_1]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [h0, h5472, h5476, hc34, hlam, hphi, ht0b, ht45, ht5b, p5727_1, u0elo0]
                                          · have p5727_0 := h5727c.1
                                            have p5727_1 := h5727c.2.1
                                            have p5727_2 := h5727c.2.2.1
                                            have p5727_3 := h5727c.2.2.2
                                            linarith only [hlam, p5727_0]
                                        · linarith only [h5415, h5654, hlam, p5482_1, u0elo1]
                                        · rcases h2bigk with h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c | h5764c
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [hlam, p5764_0]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [h0, h1, h5469, hc12, hc23, hlam, hphi, p5764_1]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [h5412, hlam, p5764_0]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            rcases p5764_3 (m.d 0 2) (by simp) with h5768 | h5768
                                            · rcases p5764_3 (m.d 1 2) (by simp) with h5769 | h5769
                                              · linarith only [h0, h5769, hlam]
                                              · linarith only [h5471, h5769, hlam]
                                            · linarith only [h5768, hlam, p5764_0]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            rcases p5764_3 (m.d 0 2) (by simp) with h5773 | h5773
                                            · rcases p5764_3 (m.d 1 2) (by simp) with h5774 | h5774
                                              · linarith only [h0, h5774, hlam]
                                              · linarith only [h5472, h5774, hlam]
                                            · linarith only [h5773, hlam, p5764_0]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [h0, hlam, p5764_0]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [hlam, p5764_0]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [h5469, hlam, p5764_0]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [h0, h1, h5469, h5476, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5764_1]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [h0, h1, h5469, h5477, h5480, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5764_1]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [h5415, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5482_1, p5764_1]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            rcases p5764_3 (m.d 0 2) (by simp) with h5784 | h5784
                                            · linarith only [h5412, h5784, hlam]
                                            · linarith only [h0, h5784, hlam]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [hlam, p5764_0]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [h0, h1, h5410, h5415, h5469, h5471, hlam, p5482_1, p5764_2]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [h0, h1, h5469, h5472, hlam, p5764_2]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [h5414, hlam, p5764_0]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [h5471, hlam, p5764_0]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [h5476, hlam, p5764_1]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [hlam, p5764_0]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [h5478, hlam, p5764_1]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [h5415, hlam, p5764_0]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [h5472, hlam, p5764_0]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [h5477, hlam, p5764_1]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [h0, h5472, h5476, hc34, hlam, hphi, ht0b, ht45, ht5b, p5764_1, u0elo0]
                                          · have p5764_0 := h5764c.1
                                            have p5764_1 := h5764c.2.1
                                            have p5764_2 := h5764c.2.2.1
                                            have p5764_3 := h5764c.2.2.2
                                            linarith only [hlam, p5764_0]
                                      · linarith only [h5418, h5653, hlam]
                                  · linarith only [h5416, h5650, hlam]
                                · linarith only [h5414, h5649, hlam]
                              · linarith only [h5410, h5648, hlam]
                            · have p5482_0 := h5482c.1
                              have p5482_1 := h5482c.2.1
                              have p5482_2 := h5482c.2.2.1
                              have p5482_3 := h5482c.2.2.2
                              linarith only [hlam, p5482_0]
                      · linarith only [h0, h1, h5469, h5477, hc12, hc35, hlam, hphi, ht23]
                    · linarith only [h0, h1, h5469, h5476, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h0, h1, h5416, h5471, h5473, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
              · linarith only [h0, h5415, h5471, h5472, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · linarith only [h0, h1, h5414, h5469, h5471, hc12, hc23, hlam, hphi]
      · linarith only [h0, h1, h5415, h5417, hlam]
    · linarith only [h1, h5410, h5416, hlam]
  · rcases m.htr 0 3 4 (by decide) (by decide) with h5812 | h5812
    · rcases m.htr 0 3 5 (by decide) (by decide) with h5813 | h5813
      · rcases m.htr 0 4 5 (by decide) (by decide) with h5814 | h5814
        · linarith only [h5414, h5415, h5814, hlam]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h5816 | h5816
          · linarith only [h0, h1, h5412, h5414, h5816, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5818 | h5818
            · rcases m.htr 1 2 5 (by decide) (by decide) with h5819 | h5819
              · linarith only [h0, h5415, h5819, hlam]
              · rcases m.htr 1 3 4 (by decide) (by decide) with h5821 | h5821
                · rcases m.htr 1 4 5 (by decide) (by decide) with h5822 | h5822
                  · linarith only [h1, h5410, h5814, h5816, h5822, hc04, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h5824 | h5824
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h5825 | h5825
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h5826 | h5826
                        · linarith only [h0, h5814, h5818, h5826, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h5828 | h5828
                          · linarith only [h1, h5411, h5415, h5816, h5818, h5819, h5824, h5826, h5828, hc02, hc23, hlam, hphi]
                          · rcases h0bigk with h5830c | h5830c | h5830c | h5830c | h5830c | h5830c | h5830c | h5830c | h5830c | h5830c | h5830c | h5830c | h5830c | h5830c | h5830c | h5830c | h5830c | h5830c | h5830c | h5830c | h5830c | h5830c | h5830c | h5830c | h5830c
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [hlam, p5830_0]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [h0, h1, h5816, h5818, h5824, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5830_1]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [h1, hlam, p5830_0]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              rcases p5830_3 (m.d 0 1) (by simp) with h5834 | h5834
                              · rcases p5830_3 (m.d 0 2) (by simp) with h5835 | h5835
                                · linarith only [h0, h5835, hlam]
                                · linarith only [h5414, h5835, hlam]
                              · linarith only [h5410, h5834, hlam]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [h0, h1, h5415, h5816, h5818, h5824, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p5830_1]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [h0, hlam, p5830_0]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [hlam, p5830_0]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [h5412, hlam, p5830_0]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [h5410, h5415, h5818, h5824, h5826, hc34, hc45, hlam, hphi, p5830_1]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [h5415, hlam, p5830_0]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [h0, h5818, h5824, hc34, hlam, hphi, ht0b, ht45, ht5b, p5830_1, u0elo2]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [h0, h5818, h5824, hc34, hlam, hphi, ht0b, ht45, ht5b, p5830_1, u0elo2]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [hlam, p5830_0]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              rcases p5830_3 (m.d 0 1) (by simp) with h5848 | h5848
                              · linarith only [h1, h5848, hlam]
                              · linarith only [h5410, h5848, hlam]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [h0, h5415, h5818, h5824, hc34, hlam, hphi, ht0b, ht45, ht5b, p5830_1, u0elo2]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [h5410, hlam, p5830_0]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [h5414, hlam, p5830_0]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [h5812, hlam, p5830_0]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [hlam, p5830_0]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [h5814, hlam, p5830_0]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [h5411, hlam, p5830_0]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [h0, h5818, h5824, hc34, hlam, hphi, ht0b, ht45, ht5b, p5830_1, u0elo4]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [h5813, hlam, p5830_0]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              rcases p5830_3 (m.d 0 1) (by simp) with h5860 | h5860
                              · rcases p5830_3 (m.d 0 2) (by simp) with h5861 | h5861
                                · linarith only [h5415, h5861, hlam]
                                · linarith only [h5414, h5861, hlam]
                              · linarith only [h5410, h5860, hlam]
                            · have p5830_0 := h5830c.1
                              have p5830_1 := h5830c.2.1
                              have p5830_2 := h5830c.2.2.1
                              have p5830_3 := h5830c.2.2.2
                              linarith only [hlam, p5830_0]
                      · linarith only [h1, h5813, h5816, h5825, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h1, h5411, h5816, h5818, h5819, h5824, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                · linarith only [h1, h5411, h5414, h5812, h5818, h5819, h5821, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
            · linarith only [h1, h5411, h5414, h5415, h5816, h5818, hc12, hc23, hlam, hphi]
      · linarith only [h1, h5411, h5813, hlam]
    · linarith only [h1, h5411, h5414, h5415, h5812, hlam]

end R2N4
