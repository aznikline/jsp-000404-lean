import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_17S8

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 11382000 in
set_option maxHeartbeats 11382000 in
theorem r1l7_20_12_14_H_I_L_I_L_I_s1 (m : N7Model)
    (hb0 : CMSig2_7_H_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
    (hg0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (hg1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0emin := hb0.2.1
  have h2bigk := hb2.1
  have h4bigk := hb4.1
  have h0 := hg0
  have h1 := hg1
  rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
  · exact r1l7_20_12_14_H_I_L_I_L_I_s2 m hb0 hb2 hb4 h0 h1 h2
  · rcases m.htr 0 1 5 (by decide) (by decide) with h5412 | h5412
    · rcases m.htr 0 2 3 (by decide) (by decide) with h5413 | h5413
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5414 | h5414
        · linarith only [h0, h2, h5414, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5416 | h5416
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5417 | h5417
            · linarith only [h1, h2, h5417, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5419 | h5419
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5420 | h5420
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5421 | h5421
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5422 | h5422
                    · linarith only [h0, h2, h5414, h5416, h5422, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5424 | h5424
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5425 | h5425
                        · linarith only [h1, h2, h5417, h5422, h5425, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · linarith only [h0, h2, h5421, h5425, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h2, h5416, h5421, h5422, h5424, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h5413, h5414, h5421, hc12, hc24, hlam, hphi]
                · linarith only [h2, h5412, h5420, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5431 | h5431
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5432 | h5432
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5433 | h5433
                    · linarith only [h0, h5414, h5433, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5435 | h5435
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5436 | h5436
                        · linarith only [h1, h5417, h5436, hlam]
                        · linarith only [h0, h2, h5432, h5436, hc23, hc34, hlam, hphi]
                      · linarith only [h0, h2, h5416, h5432, h5433, h5435, hc23, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                  · linarith only [h5413, h5414, h5432, hc12, hc24, hlam, hphi]
                · linarith only [h0, h2, h5416, h5431, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5442 | h5442
            · linarith only [h1, h2, h5442, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5444 | h5444
              · linarith only [h5413, h5416, h5444, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5446 | h5446
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5447 | h5447
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5448 | h5448
                    · linarith only [h0, h2, h5414, h5448, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5450 | h5450
                      · linarith only [h0, h5416, h5450, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5452 | h5452
                        · linarith only [h1, h2, h5442, h5452, hlam]
                        · linarith only [h0, h2, h5447, h5452, hc23, hc34, hlam, hphi]
                  · linarith only [h5413, h5414, h5447, hc12, hc24, hlam, hphi]
                · linarith only [h2, h5412, h5446, hlam]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5457 | h5457
        · linarith only [h0, h2, h5457, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5459 | h5459
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5460 | h5460
            · linarith only [h1, h2, h5460, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5462 | h5462
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5463 | h5463
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5464 | h5464
                  · linarith only [h0, h2, h5413, h5459, h5464, hc14, hc25, hlam, hphi, ht01, ht0b, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5466 | h5466
                    · linarith only [h0, h5457, h5466, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5468 | h5468
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5469 | h5469
                        · linarith only [h1, h2, h5460, h5469, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h5471 | h5471
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h5472 | h5472
                            · linarith only [h0, h2, h5469, h5472, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h5474 | h5474
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5475 | h5475
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h5476 | h5476
                                  · rcases h0bigk with h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c | h5477c
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [hlam, p5477_0]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [h2, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5477_1]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [h2, h5413, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5477_1]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [h2, hlam, p5477_1]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [h2, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p5477_1]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [h0, hlam, p5477_0]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [hlam, p5477_0]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [h5413, hlam, p5477_0]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [h5457, hlam, p5477_1]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [h0, h2, h5412, hc14, hc15, hlam, hphi, ht01, ht0b, ht5b, p5477_1]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [h1, hlam, p5477_1]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [h0, h5468, h5474, h5476, hc03, hc45, hlam, hphi, ht0b, ht5b, p5477_1]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [hlam, p5477_0]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [h5460, hlam, p5477_1]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [h5413, h5459, h5472, h5474, h5476, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5477_1]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [h1, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p5477_1]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [h0, h5457, h5468, h5472, h5474, h5476, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p5477_1]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [h5457, h5472, hc03, hc34, hlam, hphi, p5477_1]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [hlam, p5477_0]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      rcases p5477_3 (m.d 0 1) (by simp) with h5497 | h5497
                                      · linarith only [h2, h5497, hlam]
                                      · linarith only [h5412, h5497, hlam]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [h5412, hlam, p5477_0]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [h5459, hlam, p5477_1]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [h5462, hlam, p5477_0]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [h5463, hlam, p5477_1]
                                    · have p5477_0 := h5477c.1
                                      have p5477_1 := h5477c.2.1
                                      have p5477_2 := h5477c.2.2.1
                                      have p5477_3 := h5477c.2.2.2
                                      linarith only [hlam, p5477_0]
                                  · linarith only [h1, h2, h5464, h5466, h5468, h5472, h5474, h5476, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                                · linarith only [h1, h2, h5412, h5464, h5466, h5468, h5471, h5474, h5475, hc05, hc35, hlam, hphi, ht0b, ht5b]
                              · linarith only [h0, h5413, h5462, h5468, h5474, hc03, hc25, hlam, hphi, ht0b, ht5b]
                          · linarith only [h1, h2, h5464, h5468, h5471, hc25, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                      · linarith only [h5413, h5459, h5468, hc12, hc23, hlam, hphi]
                · linarith only [h1, h2, h5413, h5459, h5463, hlam]
              · linarith only [h5413, h5459, h5462, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5512 | h5512
            · linarith only [h1, h2, h5512, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5514 | h5514
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5515 | h5515
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5516 | h5516
                  · linarith only [h0, h2, h5413, h5516, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5518 | h5518
                    · linarith only [h0, h2, h5457, h5518, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5520 | h5520
                      · linarith only [h1, h2, h5459, h5516, h5518, h5520, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5522 | h5522
                        · linarith only [h1, h2, h5512, h5518, h5522, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h5524 | h5524
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h5525 | h5525
                            · linarith only [h0, h2, h5522, h5525, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h5527 | h5527
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5528 | h5528
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h5529 | h5529
                                  · rcases h0bigk with h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c | h5530c
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [hlam, p5530_0]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h0, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5530_1]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h2, h5514, h5529, hc14, hc45, hlam, hphi, ht01, ht0b, ht5b, p5530_1]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h2, hlam, p5530_1]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h2, hc05, hc14, hlam, hphi, ht01, ht0b, ht5b, p5530_1]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h0, hlam, p5530_0]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [hlam, p5530_0]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h5413, hlam, p5530_0]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h5457, hlam, p5530_1]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h5459, hlam, p5530_0]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h1, hlam, p5530_1]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h0, h1, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5530_1]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [hlam, p5530_0]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h5512, hlam, p5530_1]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h0, h5413, h5459, h5525, hc12, hc34, hlam, hphi, ht23, p5530_1]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h1, hc04, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p5530_1]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h0, h5457, h5525, hc12, hc34, hlam, hphi, ht23, p5530_1]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h5457, h5525, hc03, hc34, hlam, hphi, p5530_1]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [hlam, p5530_0]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h0, h5457, h5459, h5525, hc12, hc34, hlam, hphi, ht23, p5530_1]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h5412, hlam, p5530_0]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h0, h2, h5412, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5530_1]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h5514, hlam, p5530_0]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [h5515, hlam, p5530_1]
                                    · have p5530_0 := h5530c.1
                                      have p5530_1 := h5530c.2.1
                                      have p5530_2 := h5530c.2.2.1
                                      have p5530_3 := h5530c.2.2.2
                                      linarith only [hlam, p5530_0]
                                  · linarith only [h0, h2, h5518, h5525, h5529, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h1, h2, h5516, h5518, h5528, hc12, hc45, hlam, hphi, ht23, ht34]
                              · linarith only [h1, h2, h5514, h5518, h5525, h5527, hc23, hc34, hlam, hphi]
                          · linarith only [h1, h2, h5516, h5524, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h1, h2, h5514, h5515, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5561 | h5561
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5562 | h5562
                  · linarith only [h0, h5413, h5562, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5564 | h5564
                    · linarith only [h1, h2, h5457, h5562, h5564, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5566 | h5566
                      · linarith only [h0, h5459, h5566, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5568 | h5568
                        · linarith only [h1, h2, h5512, h5568, hc03, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h5570 | h5570
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h5571 | h5571
                            · linarith only [h1, h2, h5562, h5568, h5571, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h5573 | h5573
                              · linarith only [h1, h5514, h5562, h5571, h5573, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5575 | h5575
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h5576 | h5576
                                  · rcases h0bigk with h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c | h5577c
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [hlam, p5577_0]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h0, h2, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5577_1]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h1, h2, h5562, h5564, hc12, hc24, hlam, hphi, p5577_1]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h2, hlam, p5577_1]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h2, h5564, hc05, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, p5577_1]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h0, hlam, p5577_0]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [hlam, p5577_0]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h5413, hlam, p5577_0]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h5457, hlam, p5577_1]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h5459, hlam, p5577_0]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h1, hlam, p5577_1]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h0, h1, h2, h5564, hc12, hc24, hlam, hphi, p5577_1]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [hlam, p5577_0]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h5512, hlam, p5577_1]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h5514, hlam, p5577_1]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h5412, hc04, hc15, hlam, hphi, ht0b, ht5b, p5577_1]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h0, h2, h5564, hc12, hc24, hlam, hphi, p5577_1]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h5512, hc03, hc34, hlam, hphi, p5577_1]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [hlam, p5577_0]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h1, h5512, h5514, h5562, hc12, hc34, hlam, hphi, ht23, p5577_1]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h5412, hlam, p5577_0]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h0, h2, h5412, h5564, hc12, hc24, hlam, hphi, p5577_1]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h1, h2, h5412, h5562, h5564, hc12, hc24, hlam, hphi, p5577_1]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [h5561, hlam, p5577_1]
                                    · have p5577_0 := h5577c.1
                                      have p5577_1 := h5577c.2.1
                                      have p5577_2 := h5577c.2.2.1
                                      have p5577_3 := h5577c.2.2.2
                                      linarith only [hlam, p5577_0]
                                  · linarith only [h0, h2, h5564, h5571, h5576, hc12, hc45, hlam, hphi, ht23, ht34]
                                · linarith only [h2, h5412, h5564, h5570, h5575, hlam]
                          · linarith only [h2, h5412, h5566, h5570, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h2, h5412, h5561, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h5607 | h5607
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5608 | h5608
        · linarith only [h0, h2, h5608, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5610 | h5610
          · linarith only [h0, h5412, h5610, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5612 | h5612
            · linarith only [h1, h2, h5612, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5614 | h5614
              · linarith only [h0, h5412, h5607, h5614, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5616 | h5616
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5617 | h5617
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5618 | h5618
                    · linarith only [h0, h2, h5608, h5618, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5620 | h5620
                      · linarith only [h0, h5412, h5610, h5620, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5622 | h5622
                        · linarith only [h1, h5412, h5612, h5616, h5622, hlam]
                        · linarith only [h0, h2, h5617, h5622, hc23, hc34, hlam, hphi]
                  · linarith only [h5607, h5608, h5617, hc12, hc24, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5626 | h5626
                  · linarith only [h0, h2, h5616, h5626, hc23, hc45, hlam, hphi, ht34]
                  · linarith only [h0, h2, h5607, h5616, h5626, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 2 4 (by decide) (by decide) with h5629 | h5629
        · linarith only [h1, h2, h5607, h5629, hlam]
        · rcases m.htr 0 2 5 (by decide) (by decide) with h5631 | h5631
          · linarith only [h1, h5412, h5607, h5631, hlam]
          · rcases m.htr 0 3 4 (by decide) (by decide) with h5633 | h5633
            · linarith only [h1, h2, h5633, hlam]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h5635 | h5635
              · linarith only [h1, h5412, h5635, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h5637 | h5637
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5638 | h5638
                  · linarith only [h0, h2, h5607, h5638, hc02, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5640 | h5640
                    · linarith only [h0, h5412, h5629, h5637, h5640, hlam]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5642 | h5642
                      · linarith only [h1, h2, h5631, h5638, h5640, h5642, hc02, hc24, hlam, hphi]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5644 | h5644
                        · linarith only [h1, h2, h5633, h5640, h5644, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h5646 | h5646
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h5647 | h5647
                            · linarith only [h0, h5412, h5644, h5646, h5647, hc12, hc23, hlam, hphi]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h5649 | h5649
                              · linarith only [h1, h5412, h5635, h5638, h5647, h5649, hc12, hc34, hlam, hphi, ht23]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h5651 | h5651
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h5652 | h5652
                                  · rcases h0bigk with h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c | h5653c
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [hlam, p5653_0]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h0, h5412, h5646, hc12, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p5653_1]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h0, h5412, h5607, h5640, h5646, hc12, hc24, hlam, hphi, p5653_1]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h2, hlam, p5653_1]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h5412, hlam, p5653_1]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h0, hlam, p5653_0]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [hlam, p5653_0]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h5607, hlam, p5653_0]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h5629, hlam, p5653_1]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h5631, hlam, p5653_0]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h1, hlam, p5653_1]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h0, h1, h5412, h5640, h5646, hc12, hc24, hlam, hphi, p5653_1]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [hlam, p5653_0]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h5633, hlam, p5653_1]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h5635, hlam, p5653_1]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h0, hc04, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5653_1]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h0, h2, h5640, hc12, hc24, hlam, hphi, p5653_1]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h1, h2, h5638, h5640, hc12, hc24, hlam, hphi, p5653_1]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [hlam, p5653_0]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h1, h2, h5412, h5638, h5640, hc12, hc24, hlam, hphi, p5653_1]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h1, h5638, hc05, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p5653_1]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h0, h5412, h5640, h5646, hc12, hc24, hlam, hphi, p5653_1]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h1, h5412, h5638, h5640, h5646, hc12, hc24, hlam, hphi, p5653_1]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [h5637, hlam, p5653_1]
                                    · have p5653_0 := h5653c.1
                                      have p5653_1 := h5653c.2.1
                                      have p5653_2 := h5653c.2.2.1
                                      have p5653_3 := h5653c.2.2.2
                                      linarith only [hlam, p5653_0]
                                  · linarith only [h2, h5637, h5640, h5647, h5652, hlam]
                                · linarith only [h2, h5637, h5640, h5651, hlam]
                          · linarith only [h2, h5637, h5646, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h5682 | h5682
                  · linarith only [h0, h2, h5637, h5682, hc23, hc45, hlam, hphi, ht34]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h5684 | h5684
                    · linarith only [h1, h2, h5637, h5682, h5684, hc24, hc45, hlam, hphi]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h5686 | h5686
                      · linarith only [h0, h5631, h5686, hlam]
                      · rcases m.htr 1 3 4 (by decide) (by decide) with h5688 | h5688
                        · linarith only [h1, h2, h5637, h5688, hc34, hc45, hlam, hphi]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h5690 | h5690
                          · linarith only [h1, h2, h5637, h5682, h5684, h5690, hc12, hc24, hlam, hphi]
                          · linarith only [h1, h2, h5682, h5690, hc12, hc45, hlam, hphi, ht23, ht34]

end R2N4
