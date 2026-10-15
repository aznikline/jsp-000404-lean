import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_29S5

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 10236000 in
set_option maxHeartbeats 10236000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h4 : (m.d 2 3 + m.lam ≤ m.d 0 2 ∧ m.d 2 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 2))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 4 (by decide) (by decide) with h401 | h401
  · rcases m.htr 0 2 5 (by decide) (by decide) with h402 | h402
    · rcases m.htr 0 3 4 (by decide) (by decide) with h403 | h403
      · rcases m.htr 0 3 5 (by decide) (by decide) with h404 | h404
        · rcases m.htr 0 4 5 (by decide) (by decide) with h405 | h405
          · rcases m.htr 1 2 3 (by decide) (by decide) with h406 | h406
            · linarith only [h0, h4, h406, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h408 | h408
              · rcases m.htr 1 2 5 (by decide) (by decide) with h409 | h409
                · rcases m.htr 1 3 4 (by decide) (by decide) with h410 | h410
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h411 | h411
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h412 | h412
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h413 | h413
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h414 | h414
                          · linarith only [h0, h408, h414, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h416 | h416
                            · linarith only [h412, h414, h416, hlam]
                            · rcases h0bigk with h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c | h418c
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h0, h409, hc25, hlam, hphi, ht0b, ht5b, p418_1, u0elo0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h0, h4, h409, h413, hc35, hlam, hphi, ht0b, ht5b, p418_1, u0elo0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h405, h412, h414, hc34, hlam, hphi, ht0b, ht45, ht5b, p418_1, u0elo0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h405, h412, h414, hc34, hlam, hphi, ht0b, ht45, ht5b, p418_1, u0elo0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h0, hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h4, hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h405, h412, h414, hc34, hlam, hphi, ht0b, ht45, ht5b, p418_1, u0elo1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h1, h4, h405, h412, h414, hc34, hlam, hphi, ht0b, ht45, ht5b, p418_1, u0elo0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h1, hlam, p418_1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h0, h1, h409, h413, hc35, hlam, hphi, ht0b, ht5b, p418_1, u0elo0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h1, h405, h412, h414, hc34, hlam, hphi, ht0b, ht45, ht5b, p418_1, u0elo0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h1, h405, h412, h414, hc34, hlam, hphi, ht0b, ht45, ht5b, p418_1, u0elo0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h2, hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h401, hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h403, hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h401, h405, h412, h414, hc34, hlam, hphi, ht0b, ht45, ht5b, p418_1, u0elo1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h3, hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h402, hlam, p418_1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h404, hlam, p418_0]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [h405, hlam, p418_1]
                              · have p418_0 := h418c.1
                                have p418_1 := h418c.2.1
                                have p418_2 := h418c.2.2.1
                                have p418_3 := h418c.2.2.2
                                linarith only [hlam, p418_0]
                        · linarith only [h4, h413, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h4, h403, h412, hlam]
                    · linarith only [h410, h411, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h403, h406, h408, h410, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                · linarith only [h408, h409, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h4, h401, h408, hc12, hc23, hlam, hphi]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h450 | h450
            · linarith only [h0, h4, h450, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h452 | h452
              · rcases m.htr 1 2 5 (by decide) (by decide) with h453 | h453
                · rcases m.htr 1 3 4 (by decide) (by decide) with h454 | h454
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h455 | h455
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h456 | h456
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h457 | h457
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h458 | h458
                          · linarith only [h0, h452, h458, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h460 | h460
                            · linarith only [h2, h405, h452, h456, h460, hlam]
                            · rcases h0bigk with h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c | h462c
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                linarith only [hlam, p462_0]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                linarith only [h0, h453, h456, h458, hc34, hlam, hphi, ht0b, ht45, ht5b, p462_1, u0elo0]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                linarith only [h1, h450, h453, h456, h458, hc34, hlam, hphi, ht0b, ht45, ht5b, p462_1, u0elo0]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                rcases p462_3 (m.d 0 1) (by simp) with h466 | h466
                                · rcases p462_3 (m.d 0 2) (by simp) with h467 | h467
                                  · linarith only [h0, h467, hlam]
                                  · linarith only [h401, h467, hlam]
                                · linarith only [h2, h466, hlam]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                rcases p462_3 (m.d 0 1) (by simp) with h471 | h471
                                · rcases p462_3 (m.d 0 2) (by simp) with h472 | h472
                                  · linarith only [h0, h472, hlam]
                                  · linarith only [h402, h472, hlam]
                                · linarith only [h3, h471, hlam]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                linarith only [h0, hlam, p462_0]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                linarith only [hlam, p462_0]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                linarith only [h4, hlam, p462_0]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                rcases p462_3 (m.d 0 1) (by simp) with h479 | h479
                                · rcases p462_3 (m.d 0 2) (by simp) with h480 | h480
                                  · rcases p462_3 (m.d 0 3) (by simp) with h481 | h481
                                    · rcases p462_3 (m.d 0 4) (by simp) with h482 | h482
                                      · linarith only [h401, h482, hlam]
                                      · rcases p462_3 (m.d 0 5) (by simp) with h484 | h484
                                        · linarith only [h402, h484, hlam]
                                        · linarith only [h405, h484, hlam]
                                    · linarith only [h403, h481, hlam]
                                  · linarith only [h401, h480, hlam]
                                · linarith only [h2, h479, hlam]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                rcases p462_3 (m.d 0 1) (by simp) with h490 | h490
                                · rcases p462_3 (m.d 0 2) (by simp) with h491 | h491
                                  · rcases p462_3 (m.d 0 3) (by simp) with h492 | h492
                                    · rcases p462_3 (m.d 0 4) (by simp) with h493 | h493
                                      · linarith only [h401, h493, hlam]
                                      · rcases p462_3 (m.d 0 5) (by simp) with h495 | h495
                                        · linarith only [h402, h495, hlam]
                                        · rcases h2bigk with h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c | h497c
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [hlam, p497_0]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [h453, h456, h458, hc34, hlam, hphi, ht0b, ht45, ht5b, p497_1, u0elo1]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [h4, hlam, p497_0]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            rcases p497_3 (m.d 0 2) (by simp) with h501 | h501
                                            · rcases p497_3 (m.d 1 2) (by simp) with h502 | h502
                                              · linarith only [h0, h502, hlam]
                                              · linarith only [h452, h502, hlam]
                                            · linarith only [h501, hlam, p497_0]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            rcases p497_3 (m.d 0 2) (by simp) with h506 | h506
                                            · rcases p497_3 (m.d 1 2) (by simp) with h507 | h507
                                              · linarith only [h0, h507, hlam]
                                              · linarith only [h453, h507, hlam]
                                            · linarith only [h506, hlam, p497_0]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [h0, hlam, p497_0]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [hlam, p497_0]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [h450, hlam, p497_0]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [h0, h456, hc34, hlam, hphi, ht0b, ht45, ht5b, p497_1, u0elo0]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [h1, h450, h456, h458, hc34, hlam, hphi, ht0b, ht45, ht5b, p497_1, u0elo0]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [h2, h405, h452, h456, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p462_1, p497_1]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            rcases p497_3 (m.d 0 2) (by simp) with h517 | h517
                                            · linarith only [h4, h517, hlam]
                                            · linarith only [h0, h517, hlam]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [hlam, p497_0]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [h2, h4, h405, h452, hlam, p462_1, p497_2]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [h3, h4, h453, hlam, p462_1, p497_2]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [h401, hlam, p497_0]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [h452, hlam, p497_0]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [h456, hlam, p497_1]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [hlam, p497_0]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [h458, hlam, p497_1]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [h402, hlam, p497_0]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [h453, hlam, p497_0]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [h457, hlam, p497_1]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [h3, h453, h456, hc34, hlam, hphi, ht0b, ht45, ht5b, p462_1, p497_1, u0elo1]
                                          · have p497_0 := h497c.1
                                            have p497_1 := h497c.2.1
                                            have p497_2 := h497c.2.2.1
                                            have p497_3 := h497c.2.2.2
                                            linarith only [hlam, p497_0]
                                    · linarith only [h404, h492, hlam]
                                  · linarith only [h402, h491, hlam]
                                · linarith only [h3, h490, hlam]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                linarith only [h1, hlam, p462_1]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                linarith only [h1, h401, h456, hc34, hlam, hphi, ht0b, ht45, ht5b, p462_1, u0elo0]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                linarith only [hlam, p462_0]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                rcases p462_3 (m.d 0 1) (by simp) with h539 | h539
                                · rcases p462_3 (m.d 0 2) (by simp) with h540 | h540
                                  · linarith only [h4, h540, hlam]
                                  · linarith only [h401, h540, hlam]
                                · linarith only [h2, h539, hlam]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                rcases p462_3 (m.d 0 1) (by simp) with h544 | h544
                                · rcases p462_3 (m.d 0 2) (by simp) with h545 | h545
                                  · linarith only [h4, h545, hlam]
                                  · linarith only [h402, h545, hlam]
                                · linarith only [h3, h544, hlam]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                linarith only [h2, hlam, p462_0]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                linarith only [h401, hlam, p462_0]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                linarith only [h403, hlam, p462_0]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                linarith only [hlam, p462_0]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                linarith only [h405, hlam, p462_0]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                linarith only [h3, hlam, p462_0]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                linarith only [h402, hlam, p462_1]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                linarith only [h404, hlam, p462_0]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                linarith only [h2, h452, h456, hc34, hlam, hphi, ht45, p462_1, u5elo0]
                              · have p462_0 := h462c.1
                                have p462_1 := h462c.2.1
                                have p462_2 := h462c.2.2.1
                                have p462_3 := h462c.2.2.2
                                linarith only [hlam, p462_0]
                        · linarith only [h1, h4, h455, h457, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h1, h4, h403, h456, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h450, h452, h455, hc24, hlam, hphi, ht45, u5elo3]
                  · linarith only [h1, h403, h450, h452, h454, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                · linarith only [h452, h453, hc24, hlam, hphi, ht45, u5elo2]
              · linarith only [h4, h401, h452, hc12, hc23, hlam, hphi]
        · linarith only [h4, h401, h404, hc24, hlam, hphi, ht45, u5elo3]
      · linarith only [h4, h401, h403, hlam]
    · linarith only [h401, h402, hc24, hlam, hphi, ht45, u5elo2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h568 | h568
    · rcases m.htr 0 3 4 (by decide) (by decide) with h569 | h569
      · rcases m.htr 0 3 5 (by decide) (by decide) with h570 | h570
        · rcases m.htr 0 4 5 (by decide) (by decide) with h571 | h571
          · rcases m.htr 1 2 3 (by decide) (by decide) with h572 | h572
            · linarith only [h0, h4, h572, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h574 | h574
              · linarith only [h0, h401, h574, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h576 | h576
                · rcases m.htr 1 3 4 (by decide) (by decide) with h577 | h577
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h578 | h578
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h579 | h579
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h580 | h580
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h581 | h581
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h582 | h582
                            · linarith only [h1, h577, h582, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h0, h576, h581, h582, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h401, h568, h571, h581, hlam]
                        · linarith only [h401, h579, h580, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h1, h4, h569, h576, h579, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · linarith only [h577, h578, hc34, hlam, hphi, ht45, u5elo3]
                  · linarith only [h1, h569, h572, h576, h577, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                · linarith only [h401, h568, h576, hc12, hc24, hlam, hphi]
          · linarith only [h401, h568, h571, hc25, hlam, hphi, u5elo4]
        · linarith only [h4, h568, h570, hc25, hlam, hphi, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h593 | h593
        · rcases m.htr 0 4 5 (by decide) (by decide) with h594 | h594
          · rcases m.htr 1 2 3 (by decide) (by decide) with h595 | h595
            · linarith only [h0, h4, h568, h595, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h597 | h597
              · linarith only [h0, h401, h597, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h599 | h599
                · rcases m.htr 1 3 4 (by decide) (by decide) with h600 | h600
                  · linarith only [h0, h1, h4, h569, h599, h600, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h602 | h602
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h603 | h603
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h604 | h604
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h605 | h605
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h606 | h606
                            · rcases h0bigk with h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c | h607c
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [hlam, p607_0]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [h0, h599, h604, h606, hc45, hlam, hphi, ht0b, ht5b, p607_1, u0elo0]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [h0, h4, h599, h604, h606, hc45, hlam, hphi, ht0b, ht5b, p607_1, u0elo0]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [h0, h4, h569, h599, h604, h606, hc45, hlam, hphi, ht0b, ht5b, p607_1, u0elo0]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                rcases p607_3 (m.d 0 1) (by simp) with h612 | h612
                                · rcases p607_3 (m.d 0 2) (by simp) with h613 | h613
                                  · linarith only [h0, h613, hlam]
                                  · linarith only [h568, h613, hlam]
                                · linarith only [h3, h612, hlam]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [h0, hlam, p607_0]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [hlam, p607_0]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [h4, hlam, p607_0]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [h401, hlam, p607_1]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [h4, h569, h603, hc05, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p607_1]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [h1, hlam, p607_1]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [h569, h603, hc02, hc23, hlam, hphi, p607_1]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [hlam, p607_0]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [h569, hlam, p607_1]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [h568, h569, h603, h604, h606, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p607_1]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [h2, hlam, p607_0]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [h0, h599, h604, h606, hc45, hlam, hphi, ht0b, ht5b, p607_1, u0elo3]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [h1, h569, h595, h599, h603, h604, h606, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p607_1]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [hlam, p607_0]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                rcases p607_3 (m.d 0 1) (by simp) with h631 | h631
                                · rcases p607_3 (m.d 0 2) (by simp) with h632 | h632
                                  · linarith only [h401, h632, hlam]
                                  · linarith only [h568, h632, hlam]
                                · linarith only [h3, h631, hlam]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [h3, hlam, p607_0]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [h568, hlam, p607_1]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [h593, hlam, p607_0]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [h594, hlam, p607_1]
                              · have p607_0 := h607c.1
                                have p607_1 := h607c.2.1
                                have p607_2 := h607c.2.2.1
                                have p607_3 := h607c.2.2.2
                                linarith only [hlam, p607_0]
                            · linarith only [h2, h569, h595, h599, h600, h606, hc25, hlam, hphi, u5elo4]
                          · linarith only [h1, h569, h594, h595, h599, h603, h604, h605, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                        · linarith only [h4, h604, hc02, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h644 | h644
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h645 | h645
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h646 | h646
                            · rcases h0bigk with h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c | h647c
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [hlam, p647_0]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [h0, h599, h644, h646, hc45, hlam, hphi, ht0b, ht5b, p647_1, u0elo0]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [h0, h4, h599, h644, h646, hc45, hlam, hphi, ht0b, ht5b, p647_1, u0elo0]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [h0, h401, h599, h644, h646, hc45, hlam, hphi, ht0b, ht5b, p647_1, u0elo0]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                rcases p647_3 (m.d 0 1) (by simp) with h652 | h652
                                · rcases p647_3 (m.d 0 2) (by simp) with h653 | h653
                                  · linarith only [h0, h653, hlam]
                                  · linarith only [h568, h653, hlam]
                                · linarith only [h3, h652, hlam]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [h0, hlam, p647_0]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [hlam, p647_0]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [h4, hlam, p647_0]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [h401, hlam, p647_1]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [h4, h603, hc05, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p647_1]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [h1, hlam, p647_1]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [h0, h569, h599, hc25, hlam, hphi, ht0b, ht5b, p647_1, u0elo3]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [hlam, p647_0]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [h569, hlam, p647_1]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                rcases p647_3 (m.d 0 1) (by simp) with h666 | h666
                                · rcases p647_3 (m.d 0 2) (by simp) with h667 | h667
                                  · linarith only [h4, h667, hlam]
                                  · linarith only [h568, h667, hlam]
                                · linarith only [h3, h666, hlam]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [h2, hlam, p647_0]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [h0, h2, h599, h644, h646, hc45, hlam, hphi, ht0b, ht5b, p647_1, u0elo0]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [h0, h2, h4, h599, h644, h646, hc45, hlam, hphi, ht0b, ht5b, p647_1, u0elo0]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [hlam, p647_0]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                rcases p647_3 (m.d 0 1) (by simp) with h675 | h675
                                · rcases p647_3 (m.d 0 2) (by simp) with h676 | h676
                                  · linarith only [h401, h676, hlam]
                                  · linarith only [h568, h676, hlam]
                                · linarith only [h3, h675, hlam]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [h3, hlam, p647_0]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [h568, hlam, p647_1]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [h593, hlam, p647_0]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [h594, hlam, p647_1]
                              · have p647_0 := h647c.1
                                have p647_1 := h647c.2.1
                                have p647_2 := h647c.2.2.1
                                have p647_3 := h647c.2.2.2
                                linarith only [hlam, p647_0]
                            · linarith only [h0, h4, h599, h603, h644, h646, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b]
                          · linarith only [h0, h401, h594, h599, h644, h645, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                        · linarith only [h0, h4, h599, h644, hc25, hlam, hphi, u5elo3]
                    · linarith only [h569, h593, h602, hc13, hc34, hlam, hphi]
                · linarith only [h4, h568, h599, hc12, hc23, hlam, hphi]
          · linarith only [h401, h568, h594, hc25, hlam, hphi, u5elo4]
        · linarith only [h4, h568, h593, hc25, hlam, hphi, u5elo3]
    · rcases m.htr 0 3 4 (by decide) (by decide) with h692 | h692
      · rcases m.htr 0 3 5 (by decide) (by decide) with h693 | h693
        · rcases m.htr 0 4 5 (by decide) (by decide) with h694 | h694
          · rcases m.htr 1 2 3 (by decide) (by decide) with h695 | h695
            · linarith only [h0, h568, h695, hc23, hlam, hphi, ht34, ht45, u5elo2]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h697 | h697
              · linarith only [h0, h401, h697, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h699 | h699
                · linarith only [h0, h568, h699, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h701 | h701
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h702 | h702
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h703 | h703
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h704 | h704
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h705 | h705
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h706 | h706
                            · linarith only [h1, h701, h706, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                            · rcases h0bigk with h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c | h708c
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [hlam, p708_0]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                rcases p708_3 (m.d 0 1) (by simp) with h710 | h710
                                · rcases p708_3 (m.d 0 2) (by simp) with h711 | h711
                                  · linarith only [h0, h711, hlam]
                                  · rcases p708_3 (m.d 0 3) (by simp) with h713 | h713
                                    · linarith only [h1, h713, hlam]
                                    · linarith only [h4, h713, hlam]
                                · linarith only [h0, h710, hlam]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [h692, hc34, hlam, hphi, ht0b, ht45, ht5b, p708_1, u0elo0]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [h694, h706, hc34, hlam, hphi, ht0b, ht45, ht5b, p708_1, u0elo0]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [h694, h706, hc34, hlam, hphi, ht0b, ht45, ht5b, p708_1, u0elo0]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [h0, hlam, p708_0]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [hlam, p708_0]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [h4, hlam, p708_0]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [h401, hlam, p708_1]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [h568, hlam, p708_0]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [h1, hlam, p708_1]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                rcases p708_3 (m.d 0 1) (by simp) with h726 | h726
                                · rcases p708_3 (m.d 0 2) (by simp) with h727 | h727
                                  · linarith only [h4, h727, hlam]
                                  · rcases p708_3 (m.d 0 3) (by simp) with h729 | h729
                                    · rcases p708_3 (m.d 0 4) (by simp) with h730 | h730
                                      · linarith only [h692, h730, hlam]
                                      · linarith only [h401, h730, hlam]
                                    · linarith only [h4, h729, hlam]
                                · linarith only [h0, h726, hlam]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [hlam, p708_0]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [h1, h694, h706, hc34, hlam, hphi, ht0b, ht45, ht5b, p708_1, u0elo0]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [h1, h694, h706, hc34, hlam, hphi, ht0b, ht45, ht5b, p708_1, u0elo0]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [h2, hlam, p708_0]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                rcases p708_3 (m.d 0 1) (by simp) with h739 | h739
                                · rcases p708_3 (m.d 0 2) (by simp) with h740 | h740
                                  · linarith only [h401, h740, hlam]
                                  · rcases p708_3 (m.d 0 3) (by simp) with h742 | h742
                                    · rcases p708_3 (m.d 0 4) (by simp) with h743 | h743
                                      · rcases p708_3 (m.d 0 5) (by simp) with h744 | h744
                                        · linarith only [h694, h744, hlam]
                                        · linarith only [h568, h744, hlam]
                                      · linarith only [h401, h743, hlam]
                                    · linarith only [h4, h742, hlam]
                                · linarith only [h0, h739, hlam]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [h692, hlam, p708_0]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [hlam, p708_0]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [h1, h692, h694, h706, hc34, hlam, hphi, ht0b, ht45, ht5b, p708_1, u0elo0]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [h3, hlam, p708_0]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p708_1, u5elo0]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [h693, hlam, p708_0]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [h694, hlam, p708_1]
                              · have p708_0 := h708c.1
                                have p708_1 := h708c.2.1
                                have p708_2 := h708c.2.2.1
                                have p708_3 := h708c.2.2.2
                                linarith only [hlam, p708_0]
                          · linarith only [h0, h401, h705, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h0, h4, h704, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · linarith only [h0, h1, h4, h701, h703, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h1, h693, h701, h702, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h762 | h762
                    · linarith only [h1, h692, h701, h762, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h764 | h764
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h765 | h765
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h766 | h766
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h767 | h767
                            · rcases h0bigk with h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [hlam, p768_0]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                rcases p768_3 (m.d 0 1) (by simp) with h770 | h770
                                · rcases p768_3 (m.d 0 2) (by simp) with h771 | h771
                                  · linarith only [h0, h771, hlam]
                                  · rcases p768_3 (m.d 0 3) (by simp) with h773 | h773
                                    · linarith only [h1, h773, hlam]
                                    · linarith only [h4, h773, hlam]
                                · linarith only [h0, h770, hlam]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [h692, h762, h767, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p768_1, u0elo0]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [h692, h762, h767, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p768_1, u0elo0]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [h693, h762, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p768_1, u0elo0]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [h0, hlam, p768_0]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [hlam, p768_0]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [h4, hlam, p768_0]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [h401, hlam, p768_1]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [h568, hlam, p768_0]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [h1, hlam, p768_1]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                rcases p768_3 (m.d 0 1) (by simp) with h786 | h786
                                · rcases p768_3 (m.d 0 2) (by simp) with h787 | h787
                                  · linarith only [h4, h787, hlam]
                                  · rcases p768_3 (m.d 0 3) (by simp) with h789 | h789
                                    · rcases p768_3 (m.d 0 4) (by simp) with h790 | h790
                                      · linarith only [h692, h790, hlam]
                                      · linarith only [h401, h790, hlam]
                                    · linarith only [h4, h789, hlam]
                                · linarith only [h0, h786, hlam]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [hlam, p768_0]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [h692, h695, h762, h767, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p768_1, u0elo2]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [h1, h693, h695, h762, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p768_1, u0elo0]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [h2, hlam, p768_0]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                rcases p768_3 (m.d 0 1) (by simp) with h799 | h799
                                · rcases p768_3 (m.d 0 2) (by simp) with h800 | h800
                                  · linarith only [h401, h800, hlam]
                                  · rcases p768_3 (m.d 0 3) (by simp) with h802 | h802
                                    · rcases p768_3 (m.d 0 4) (by simp) with h803 | h803
                                      · rcases p768_3 (m.d 0 5) (by simp) with h804 | h804
                                        · linarith only [h694, h804, hlam]
                                        · linarith only [h568, h804, hlam]
                                      · linarith only [h401, h803, hlam]
                                    · linarith only [h4, h802, hlam]
                                · linarith only [h0, h799, hlam]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [h692, hlam, p768_0]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [hlam, p768_0]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [h693, h695, h762, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p768_1, u0elo3]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [h3, hlam, p768_0]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p768_1, u5elo0]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [h693, hlam, p768_0]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [h694, hlam, p768_1]
                              · have p768_0 := h768c.1
                                have p768_1 := h768c.2.1
                                have p768_2 := h768c.2.2.1
                                have p768_3 := h768c.2.2.2
                                linarith only [hlam, p768_0]
                            · linarith only [h1, h692, h694, h695, h701, h767, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · linarith only [h401, h694, h766, hlam]
                        · linarith only [h4, h692, h694, h765, hc45, hlam, hphi, u5elo3]
                      · linarith only [h4, h692, h764, hlam]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h822 | h822
            · linarith only [h0, h4, h692, h822, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h824 | h824
              · linarith only [h0, h401, h824, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h826 | h826
                · linarith only [h2, h694, h824, h826, hc25, hlam, hphi, u5elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h828 | h828
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h829 | h829
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h830 | h830
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h831 | h831
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h832 | h832
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h833 | h833
                            · linarith only [h2, h692, h694, h824, h833, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · rcases h0bigk with h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c | h835c
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                linarith only [hlam, p835_0]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                rcases p835_3 (m.d 0 1) (by simp) with h837 | h837
                                · rcases p835_3 (m.d 0 2) (by simp) with h838 | h838
                                  · linarith only [h0, h838, hlam]
                                  · rcases p835_3 (m.d 0 3) (by simp) with h840 | h840
                                    · linarith only [h1, h840, hlam]
                                    · linarith only [h4, h840, hlam]
                                · linarith only [h0, h837, hlam]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                linarith only [h1, h829, hc35, hlam, hphi, ht0b, ht5b, p835_1, u0elo0]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                rcases p835_3 (m.d 0 1) (by simp) with h845 | h845
                                · rcases p835_3 (m.d 0 2) (by simp) with h846 | h846
                                  · linarith only [h0, h846, hlam]
                                  · rcases p835_3 (m.d 0 3) (by simp) with h848 | h848
                                    · linarith only [h1, h848, hlam]
                                    · linarith only [h692, h848, hlam]
                                · linarith only [h2, h845, hlam]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                rcases p835_3 (m.d 0 1) (by simp) with h852 | h852
                                · rcases p835_3 (m.d 0 2) (by simp) with h853 | h853
                                  · linarith only [h0, h853, hlam]
                                  · rcases p835_3 (m.d 0 3) (by simp) with h855 | h855
                                    · linarith only [h1, h855, hlam]
                                    · linarith only [h693, h855, hlam]
                                · linarith only [h3, h852, hlam]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                linarith only [h0, hlam, p835_0]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                linarith only [hlam, p835_0]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                linarith only [h4, hlam, p835_0]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                linarith only [h401, hlam, p835_1]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                linarith only [h568, hlam, p835_0]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                linarith only [h1, hlam, p835_1]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                rcases p835_3 (m.d 0 1) (by simp) with h865 | h865
                                · rcases p835_3 (m.d 0 2) (by simp) with h866 | h866
                                  · linarith only [h4, h866, hlam]
                                  · rcases p835_3 (m.d 0 3) (by simp) with h868 | h868
                                    · rcases p835_3 (m.d 0 4) (by simp) with h869 | h869
                                      · linarith only [h692, h869, hlam]
                                      · linarith only [h401, h869, hlam]
                                    · linarith only [h4, h868, hlam]
                                · linarith only [h0, h865, hlam]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                linarith only [hlam, p835_0]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                rcases p835_3 (m.d 0 1) (by simp) with h875 | h875
                                · rcases p835_3 (m.d 0 2) (by simp) with h876 | h876
                                  · linarith only [h4, h876, hlam]
                                  · rcases p835_3 (m.d 0 3) (by simp) with h878 | h878
                                    · rcases p835_3 (m.d 0 4) (by simp) with h879 | h879
                                      · linarith only [h692, h879, hlam]
                                      · rcases p835_3 (m.d 0 5) (by simp) with h881 | h881
                                        · linarith only [h693, h881, hlam]
                                        · linarith only [h694, h881, hlam]
                                    · linarith only [h692, h878, hlam]
                                · linarith only [h2, h875, hlam]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                rcases p835_3 (m.d 0 1) (by simp) with h886 | h886
                                · rcases p835_3 (m.d 0 2) (by simp) with h887 | h887
                                  · linarith only [h4, h887, hlam]
                                  · rcases p835_3 (m.d 0 3) (by simp) with h889 | h889
                                    · rcases p835_3 (m.d 0 4) (by simp) with h890 | h890
                                      · linarith only [h692, h890, hlam]
                                      · rcases p835_3 (m.d 0 5) (by simp) with h892 | h892
                                        · linarith only [h693, h892, hlam]
                                        · rcases h2bigk with h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c | h894c
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [hlam, p894_0]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [h4, hc12, hc23, hlam, hphi, p894_1]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [h4, hlam, p894_0]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [h401, hlam, p894_0]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [h568, hlam, p894_0]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [h0, hlam, p894_0]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [hlam, p894_0]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [h822, hlam, p894_0]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [h824, hlam, p894_0]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [h826, hlam, p894_0]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            rcases p894_3 (m.d 0 2) (by simp) with h905 | h905
                                            · linarith only [h905, hlam, p894_0]
                                            · rcases p894_3 (m.d 1 2) (by simp) with h907 | h907
                                              · linarith only [h822, h907, hlam]
                                              · rcases p894_3 (m.d 2 3) (by simp) with h909 | h909
                                                · rcases p894_3 (m.d 2 4) (by simp) with h910 | h910
                                                  · linarith only [h830, h910, hlam]
                                                  · linarith only [h401, h910, hlam]
                                                · linarith only [h909, hlam, p894_0]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            rcases p894_3 (m.d 0 2) (by simp) with h914 | h914
                                            · linarith only [h4, h914, hlam]
                                            · linarith only [h0, h914, hlam]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [hlam, p894_0]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [h2, h694, h824, h832, hc12, hc23, hlam, hphi, p894_1]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [h2, h694, h824, h832, hc12, hc23, hlam, hphi, p894_1]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            rcases p894_3 (m.d 0 2) (by simp) with h920 | h920
                                            · linarith only [h920, hlam, p894_0]
                                            · rcases p894_3 (m.d 1 2) (by simp) with h922 | h922
                                              · linarith only [h824, h922, hlam]
                                              · rcases p894_3 (m.d 2 3) (by simp) with h924 | h924
                                                · rcases p894_3 (m.d 2 4) (by simp) with h925 | h925
                                                  · rcases p894_3 (m.d 2 5) (by simp) with h926 | h926
                                                    · linarith only [h832, h926, hlam]
                                                    · linarith only [h568, h926, hlam]
                                                  · linarith only [h925, hlam, p894_0]
                                                · linarith only [h4, h924, hlam]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            rcases p894_3 (m.d 0 2) (by simp) with h931 | h931
                                            · linarith only [h401, h931, hlam]
                                            · linarith only [h0, h931, hlam]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [h830, hlam, p894_1]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [hlam, p894_0]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [h2, h694, h824, h832, hc12, hc24, hlam, hphi, p894_1]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [hc02, hlam, hphi, ht23, ht34, ht45, p894_1, u5elo2]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [hc12, hlam, hphi, ht23, ht34, ht45, p894_1, u5elo2]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [h831, hlam, p894_1]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [h832, hlam, p894_0]
                                          · have p894_0 := h894c.1
                                            have p894_1 := h894c.2.1
                                            have p894_2 := h894c.2.2.1
                                            have p894_3 := h894c.2.2.2
                                            linarith only [hlam, p894_0]
                                    · linarith only [h693, h889, hlam]
                                · linarith only [h3, h886, hlam]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                linarith only [h2, hlam, p835_0]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                linarith only [h0, h694, hc12, hc45, hlam, hphi, ht23, ht34, p835_1]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                linarith only [h692, hlam, p835_0]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                linarith only [hlam, p835_0]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                linarith only [h694, hlam, p835_0]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                linarith only [h3, hlam, p835_0]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p835_1, u5elo0]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                linarith only [h693, hlam, p835_0]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                linarith only [h568, hc04, hlam, hphi, ht45, p835_1, u5elo2]
                              · have p835_0 := h835c.1
                                have p835_1 := h835c.2.1
                                have p835_2 := h835c.2.2.1
                                have p835_3 := h835c.2.2.2
                                linarith only [hlam, p835_0]
                          · linarith only [h0, h401, h832, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h1, h829, h831, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h4, h692, h830, hlam]
                    · linarith only [h1, h693, h828, h829, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · linarith only [h692, h694, h828, hc13, hlam, hphi, ht34, ht45, u5elo4]
        · linarith only [h692, h693, hc34, hlam, hphi, ht45, u5elo3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h960 | h960
        · rcases m.htr 0 4 5 (by decide) (by decide) with h961 | h961
          · rcases m.htr 1 2 3 (by decide) (by decide) with h962 | h962
            · linarith only [h0, h4, h962, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h964 | h964
              · linarith only [h0, h401, h964, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h966 | h966
                · linarith only [h0, h568, h966, hlam]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h968 | h968
                  · linarith only [h1, h692, h960, h968, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h970 | h970
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h971 | h971
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h972 | h972
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h973 | h973
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h974 | h974
                            · rcases h0bigk with h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c | h975c
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [hlam, p975_0]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                rcases p975_3 (m.d 0 1) (by simp) with h977 | h977
                                · rcases p975_3 (m.d 0 2) (by simp) with h978 | h978
                                  · linarith only [h0, h978, hlam]
                                  · rcases p975_3 (m.d 0 3) (by simp) with h980 | h980
                                    · linarith only [h1, h980, hlam]
                                    · linarith only [h4, h980, hlam]
                                · linarith only [h0, h977, hlam]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [h1, h970, h974, hc45, hlam, hphi, ht0b, ht5b, p975_1, u0elo0]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [h1, h692, h970, h974, hc45, hlam, hphi, ht0b, ht5b, p975_1, u0elo0]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                rcases p975_3 (m.d 0 1) (by simp) with h986 | h986
                                · rcases p975_3 (m.d 0 2) (by simp) with h987 | h987
                                  · linarith only [h0, h987, hlam]
                                  · rcases p975_3 (m.d 0 3) (by simp) with h989 | h989
                                    · linarith only [h1, h989, hlam]
                                    · linarith only [h960, h989, hlam]
                                · linarith only [h3, h986, hlam]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [h0, hlam, p975_0]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [hlam, p975_0]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [h4, hlam, p975_0]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [h401, hlam, p975_1]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [h568, hlam, p975_0]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [h1, hlam, p975_1]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [h0, h692, h971, hc12, hc23, hlam, hphi, p975_1]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [hlam, p975_0]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [h692, hlam, p975_1]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [h0, h568, h692, h971, hc12, hc23, hlam, hphi, p975_1]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [h2, hlam, p975_0]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [h0, h692, h971, hc12, hc23, hlam, hphi, p975_1]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [h1, h692, h970, h971, h974, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p975_1]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [hlam, p975_0]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [h0, h568, h692, h971, hc12, hc23, hlam, hphi, p975_1]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [h3, hlam, p975_0]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p975_1, u5elo0]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [h960, hlam, p975_0]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [h961, hlam, p975_1]
                              · have p975_0 := h975c.1
                                have p975_1 := h975c.2.1
                                have p975_2 := h975c.2.2.1
                                have p975_3 := h975c.2.2.2
                                linarith only [hlam, p975_0]
                            · linarith only [h692, h974, hc03, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h692, h960, h961, h971, h973, hlam]
                        · linarith only [h1, h692, h970, h972, hc23, hc34, hlam, hphi]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1016 | h1016
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1017 | h1017
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1018 | h1018
                            · rcases h0bigk with h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c | h1019c
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [hlam, p1019_0]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                rcases p1019_3 (m.d 0 1) (by simp) with h1021 | h1021
                                · rcases p1019_3 (m.d 0 2) (by simp) with h1022 | h1022
                                  · linarith only [h0, h1022, hlam]
                                  · rcases p1019_3 (m.d 0 3) (by simp) with h1024 | h1024
                                    · linarith only [h1, h1024, hlam]
                                    · linarith only [h1024, h4, hlam]
                                · linarith only [h0, h1021, hlam]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [h960, hc35, hlam, hphi, ht0b, ht5b, p1019_1, u0elo0]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [h1018, h692, h960, hc45, hlam, hphi, ht0b, ht5b, p1019_1, u0elo0]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                rcases p1019_3 (m.d 0 1) (by simp) with h1030 | h1030
                                · rcases p1019_3 (m.d 0 2) (by simp) with h1031 | h1031
                                  · linarith only [h0, h1031, hlam]
                                  · rcases p1019_3 (m.d 0 3) (by simp) with h1033 | h1033
                                    · linarith only [h1, h1033, hlam]
                                    · linarith only [h1033, h960, hlam]
                                · linarith only [h1030, h3, hlam]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [h0, hlam, p1019_0]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [hlam, p1019_0]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [h4, hlam, p1019_0]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [h401, hlam, p1019_1]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [h568, hlam, p1019_0]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [h1, hlam, p1019_1]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [h0, h4, h971, hc12, hc34, hlam, hphi, ht23, p1019_1]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [hlam, p1019_0]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [h692, hlam, p1019_1]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [h3, h4, h966, h971, hc12, hc34, hlam, hphi, ht23, p1019_1]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [h2, hlam, p1019_0]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                rcases p1019_3 (m.d 0 1) (by simp) with h1048 | h1048
                                · rcases p1019_3 (m.d 0 2) (by simp) with h1049 | h1049
                                  · linarith only [h1049, h401, hlam]
                                  · rcases p1019_3 (m.d 0 3) (by simp) with h1051 | h1051
                                    · linarith only [h1051, h692, hlam]
                                    · linarith only [h1051, h4, hlam]
                                · linarith only [h0, h1048, hlam]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [h1, h1018, h970, hc45, hlam, hphi, ht0b, ht5b, p1019_1, u0elo3]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [hlam, p1019_0]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                rcases p1019_3 (m.d 0 1) (by simp) with h1057 | h1057
                                · rcases p1019_3 (m.d 0 2) (by simp) with h1058 | h1058
                                  · linarith only [h1058, h401, hlam]
                                  · rcases p1019_3 (m.d 0 3) (by simp) with h1060 | h1060
                                    · linarith only [h1060, h692, hlam]
                                    · linarith only [h1060, h960, hlam]
                                · linarith only [h1057, h3, hlam]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [h3, hlam, p1019_0]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p1019_1, u5elo0]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [h960, hlam, p1019_0]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [h961, hlam, p1019_1]
                              · have p1019_0 := h1019c.1
                                have p1019_1 := h1019c.2.1
                                have p1019_2 := h1019c.2.2.1
                                have p1019_3 := h1019c.2.2.2
                                linarith only [hlam, p1019_0]
                            · linarith only [h1018, h971, hc23, hlam, hphi, ht34, ht45, u5elo4]
                          · linarith only [h0, h1017, h4, h401, h960, h961, h971, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h1016, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                    · linarith only [h692, h960, h970, hc13, hc34, hlam, hphi]
          · linarith only [h692, h960, h961, hc35, hlam, hphi, u5elo4]
        · rcases m.htr 0 4 5 (by decide) (by decide) with h1074 | h1074
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1075 | h1075
            · linarith only [h0, h1075, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1077 | h1077
              · linarith only [h1, h1075, h1077, h401, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1079 | h1079
                · linarith only [h0, h1079, h4, h960, hc25, hlam, hphi, u5elo3]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1081 | h1081
                  · linarith only [h1, h1081, h960, hc34, hlam, hphi, ht45, u5elo3]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1083 | h1083
                    · linarith only [h1, h1083, h960, hlam]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1085 | h1085
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1086 | h1086
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1087 | h1087
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1088 | h1088
                            · rcases h0bigk with h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c | h1089c
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [hlam, p1089_0]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                rcases p1089_3 (m.d 0 1) (by simp) with h1091 | h1091
                                · rcases p1089_3 (m.d 0 2) (by simp) with h1092 | h1092
                                  · linarith only [h0, h1092, hlam]
                                  · rcases p1089_3 (m.d 0 3) (by simp) with h1094 | h1094
                                    · linarith only [h1, h1094, hlam]
                                    · linarith only [h1094, h4, hlam]
                                · linarith only [h0, h1091, hlam]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                rcases p1089_3 (m.d 0 1) (by simp) with h1098 | h1098
                                · rcases p1089_3 (m.d 0 2) (by simp) with h1099 | h1099
                                  · linarith only [h0, h1099, hlam]
                                  · rcases p1089_3 (m.d 0 3) (by simp) with h1101 | h1101
                                    · linarith only [h1, h1101, hlam]
                                    · rcases p1089_3 (m.d 0 4) (by simp) with h1103 | h1103
                                      · linarith only [h1103, h2, hlam]
                                      · linarith only [h1103, h692, hlam]
                                · linarith only [h1, h1098, hlam]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [h1074, hc45, hlam, hphi, ht0b, ht5b, p1089_1, u0elo0]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                rcases p1089_3 (m.d 0 1) (by simp) with h1108 | h1108
                                · rcases p1089_3 (m.d 0 2) (by simp) with h1109 | h1109
                                  · linarith only [h0, h1109, hlam]
                                  · rcases p1089_3 (m.d 0 3) (by simp) with h1111 | h1111
                                    · linarith only [h1, h1111, hlam]
                                    · rcases p1089_3 (m.d 0 4) (by simp) with h1113 | h1113
                                      · linarith only [h1113, h2, hlam]
                                      · linarith only [h1074, h1113, hlam]
                                · linarith only [h1108, h3, hlam]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [h0, hlam, p1089_0]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [hlam, p1089_0]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [h4, hlam, p1089_0]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [h401, hlam, p1089_1]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [h568, hlam, p1089_0]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [h1, hlam, p1089_1]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [h0, h960, hc12, hlam, hphi, ht23, ht34, ht45, p1089_1, u5elo0]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [hlam, p1089_0]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [h692, hlam, p1089_1]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [h960, hlam, p1089_1]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [h2, hlam, p1089_0]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [h0, h1085, h692, hc12, hc23, hlam, hphi, p1089_1]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [h0, h1085, h4, h692, hc12, hc23, hlam, hphi, p1089_1]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [hlam, p1089_0]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [h0, h1085, h4, h692, h960, hc12, hc23, hlam, hphi, p1089_1]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [h3, hlam, p1089_0]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [h0, hc12, hlam, hphi, ht23, ht34, ht45, p1089_1, u5elo0]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [h0, h1086, h4, h960, hc12, hlam, hphi, ht23, ht34, ht45, p1089_1, u5elo2]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [h1074, hlam, p1089_1]
                              · have p1089_0 := h1089c.1
                                have p1089_1 := h1089c.2.1
                                have p1089_2 := h1089c.2.2.1
                                have p1089_3 := h1089c.2.2.2
                                linarith only [hlam, p1089_0]
                            · linarith only [h0, h1088, h4, h692, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                          · linarith only [h0, h1087, h401, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h0, h1086, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1140 | h1140
                        · linarith only [h0, h1085, h1140, h4, h960, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h1140, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h1143 | h1143
            · linarith only [h0, h1143, h4, hlam]
            · rcases m.htr 1 2 4 (by decide) (by decide) with h1145 | h1145
              · linarith only [h0, h1145, h401, hlam]
              · rcases m.htr 1 2 5 (by decide) (by decide) with h1147 | h1147
                · linarith only [h0, h1074, h1147, h4, h568, h692, hc05, hlam, hphi, u5elo4]
                · rcases m.htr 1 3 4 (by decide) (by decide) with h1149 | h1149
                  · linarith only [h1, h1074, h1149, h692, hc34, hlam, hphi, ht45, u5elo4]
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h1151 | h1151
                    · linarith only [h1, h1074, h1151, h692, hc35, hlam, hphi, u5elo4]
                    · rcases m.htr 2 3 4 (by decide) (by decide) with h1153 | h1153
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1154 | h1154
                        · rcases m.htr 2 4 5 (by decide) (by decide) with h1155 | h1155
                          · rcases m.htr 3 4 5 (by decide) (by decide) with h1156 | h1156
                            · linarith only [h0, h1074, h1153, h1156, h4, h692, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1155, h1156, h4, h692, hc12, hlam, hphi, ht23, ht34, ht45, u5elo2]
                          · linarith only [h0, h1155, h401, hc12, hlam, hphi, ht23, ht34, ht45, u5elo4]
                        · linarith only [h0, h1154, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]
                      · rcases m.htr 2 3 5 (by decide) (by decide) with h1161 | h1161
                        · linarith only [h0, h1153, h1161, h4, h960, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h1161, h4, hc12, hlam, hphi, ht23, ht34, ht45, u5elo3]

set_option maxHeartbeats 10236000 in
set_option maxHeartbeats 10236000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3 h4

set_option maxHeartbeats 10236000 in
set_option maxHeartbeats 10236000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
    (h3 : (m.d 1 5 + m.lam ≤ m.d 0 1 ∧ m.d 1 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 1))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  linarith only [h0, h3, hc12, hlam, hphi, ht23, ht34, ht45, u5elo1]

set_option maxHeartbeats 10236000 in
set_option maxHeartbeats 10236000 in
theorem r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig2_7_M_LI m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_0 m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 4 ∧ m.d 0 1 < m.d 0 4 ∧ m.d 0 4 < m.d 1 4))
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
  have h0bigk := hb0.2.2.2
  have h2bigk := hb2.1
  have h2emin := hb2.2.1
  have h3bigk := hb3.1
  have h5elo := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u5elo0 := h5elo (m.d 0 5) (by simp)
  have u5elo1 := h5elo (m.d 1 5) (by simp)
  have u5elo2 := h5elo (m.d 2 5) (by simp)
  have u5elo3 := h5elo (m.d 3 5) (by simp)
  have u5elo4 := h5elo (m.d 4 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x0_x0_x0_x0 m hb0 hb2 hb3 hb5 h0 h1 h2 h3
  · exact r1l7_20_12_13_15_M_LI_L_I_L_I_L_0_x0_x0_x0_x1 m hb0 hb2 hb3 hb5 h0 h1 h2 h3

end R2N4
