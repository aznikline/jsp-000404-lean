import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_52S0

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4970000 in
theorem r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
    (h5 : (m.d 3 4 + m.lam ≤ m.d 0 3 ∧ m.d 3 4 < m.d 0 4 ∧ m.d 0 4 < m.d 0 3))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 5 (by decide) (by decide) with h415 | h415
  · rcases m.htr 0 4 5 (by decide) (by decide) with h416 | h416
    · rcases m.htr 1 2 3 (by decide) (by decide) with h417 | h417
      · rcases m.htr 1 2 5 (by decide) (by decide) with h418 | h418
        · rcases m.htr 1 3 4 (by decide) (by decide) with h419 | h419
          · linarith only [h1, h415, h419, h5, hc01, hc35, hlam, hphi, ht0b, ht5b]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h421 | h421
            · rcases m.htr 1 4 5 (by decide) (by decide) with h422 | h422
              · rcases m.htr 2 3 5 (by decide) (by decide) with h423 | h423
                · rcases m.htr 3 4 5 (by decide) (by decide) with h424 | h424
                  · rcases h0emin with h425 | h425 | h425 | h425 | h425
                    · rcases h5bigk with h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c | h426c
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [hlam, p426_0]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h415, h418, h5, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p426_1]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h415, h5, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p426_1]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h415, h5, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p426_1]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h415, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p426_1]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h2, hlam, p426_0]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [hlam, p426_0]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p426_1]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h2, h415, h424, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p426_1]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h2, h415, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p426_1]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h4, hlam, p426_1]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h418, hlam, p426_1]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [hlam, p426_0]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h424, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p426_1, u2elo4]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h0, h417, h423, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p426_1, u2elo0]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h415, hlam, p426_0]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h421, hlam, p426_0]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h423, hlam, p426_0]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [hlam, p426_0]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h415, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p426_1]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h416, hlam, p426_0]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h422, hlam, p426_0]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h416, hc04, hc25, hlam, hphi, ht0b, ht5b, p426_1]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [h424, hlam, p426_0]
                      · have p426_0 := h426c.1
                        have p426_1 := h426c.2.1
                        have p426_2 := h426c.2.2.1
                        have p426_3 := h426c.2.2.2
                        linarith only [hlam, p426_0]
                    · linarith only [h425, hlam, ht01, ht12, u2elo0]
                    · linarith only [h425, h5, hc34, hlam, ht01, ht12, ht23]
                    · rcases h5bigk with h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c | h454c
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h415, h5, hc15, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h415, h5, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h415, h424, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h415, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h2, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h2, h423, h424, hc01, hc45, hlam, hphi, ht0b, ht5b, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h2, h415, h424, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h2, h415, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h4, hlam, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h418, hlam, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h424, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p454_1, u2elo4]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h0, h417, h423, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p454_1, u2elo0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h415, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h421, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h423, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h415, h5, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h416, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h422, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h416, hc04, hc25, hlam, hphi, ht0b, ht5b, p454_1]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [h424, hlam, p454_0]
                      · have p454_0 := h454c.1
                        have p454_1 := h454c.2.1
                        have p454_2 := h454c.2.2.1
                        have p454_3 := h454c.2.2.2
                        linarith only [hlam, p454_0]
                    · linarith only [h415, h425, h5, hc34, hlam, ht01, ht12, ht23]
                  · linarith only [h2, h415, h422, h424, h5, hlam]
                · linarith only [h415, h423, h5, hc23, hc34, hlam, hphi]
              · linarith only [h419, h421, h422, hlam]
            · linarith only [h415, h421, h5, hc13, hc34, hlam, hphi]
        · linarith only [h4, h418, hc12, hlam, hphi, u2elo0]
      · linarith only [h3, h417, hc12, hlam, hphi, u2elo0]
    · linarith only [h415, h416, h5, hlam]
  · rcases m.htr 0 4 5 (by decide) (by decide) with h488 | h488
    · rcases m.htr 1 2 3 (by decide) (by decide) with h489 | h489
      · rcases m.htr 1 2 5 (by decide) (by decide) with h490 | h490
        · rcases m.htr 1 3 4 (by decide) (by decide) with h491 | h491
          · linarith only [h1, h491, h5, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h493 | h493
            · linarith only [h1, h415, h493, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h495 | h495
              · rcases m.htr 2 3 5 (by decide) (by decide) with h496 | h496
                · linarith only [h1, h415, h489, h496, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h498 | h498
                  · rcases h0emin with h499 | h499 | h499 | h499 | h499
                    · rcases h5bigk with h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c | h500c
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [hlam, p500_0]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [h4, h489, h493, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p500_1, u2elo0]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [h4, h496, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p500_1, u2elo0]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [h415, hlam, p500_1]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p500_1, u2elo0]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [h2, hlam, p500_0]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [hlam, p500_0]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [h2, h496, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p500_1]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [h493, hlam, p500_1]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [h2, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p500_1, u2elo0]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [h4, hlam, p500_1]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [h490, hlam, p500_1]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [hlam, p500_0]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [h496, hlam, p500_1]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p500_1, u2elo4]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [h1, h415, h489, h498, hc23, hc34, hlam, hphi, p500_1]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [h489, h493, h498, hc23, hc34, hlam, hphi, p500_1]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [h496, h498, hc23, hc34, hlam, hphi, p500_1]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [hlam, p500_0]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        rcases p500_3 (m.d 0 5) (by simp) with h520 | h520
                        · linarith only [h415, h520, hlam]
                        · linarith only [h488, h520, hlam]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [h488, hlam, p500_0]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [h495, hlam, p500_0]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [h488, h496, hc04, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p500_1]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [h498, hlam, p500_0]
                      · have p500_0 := h500c.1
                        have p500_1 := h500c.2.1
                        have p500_2 := h500c.2.2.1
                        have p500_3 := h500c.2.2.2
                        linarith only [hlam, p500_0]
                    · linarith only [h499, hlam, ht01, ht12, u2elo0]
                    · linarith only [h3, h499, hlam, ht01, ht12, u2elo0]
                    · rcases h5bigk with h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c | h530c
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [hlam, p530_0]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [h4, h489, h493, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p530_1, u2elo0]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [h4, h496, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p530_1, u2elo0]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [h415, hlam, p530_1]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p530_1, u2elo0]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [h2, hlam, p530_0]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [hlam, p530_0]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [h2, h496, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p530_1]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [h493, hlam, p530_1]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [h2, h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p530_1, u2elo0]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [h4, hlam, p530_1]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [h490, hlam, p530_1]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [hlam, p530_0]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [h496, hlam, p530_1]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p530_1, u2elo4]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [h415, h498, hc03, hc34, hlam, hphi, p530_1]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [h489, h493, h498, hc23, hc34, hlam, hphi, p530_1]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [h496, h498, hc23, hc34, hlam, hphi, p530_1]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [hlam, p530_0]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        rcases p530_3 (m.d 0 5) (by simp) with h550 | h550
                        · linarith only [h415, h550, hlam]
                        · linarith only [h488, h550, hlam]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [h488, hlam, p530_0]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [h495, hlam, p530_0]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [h496, hc23, hc45, hlam, hphi, ht34, p530_1]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [h498, hlam, p530_0]
                      · have p530_0 := h530c.1
                        have p530_1 := h530c.2.1
                        have p530_2 := h530c.2.2.1
                        have p530_3 := h530c.2.2.2
                        linarith only [hlam, p530_0]
                    · linarith only [h4, h499, hlam, ht01, ht12, u2elo0]
                  · linarith only [h488, h498, h5, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h560 | h560
                · linarith only [h1, h415, h489, h560, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h562 | h562
                  · rcases h0emin with h563 | h563 | h563 | h563 | h563
                    · rcases h5bigk with h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c | h564c
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [hlam, p564_0]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p564_1, u2elo0]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p564_1, u2elo0]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h415, hlam, p564_1]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h4, h495, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p564_1, u2elo0]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h2, hlam, p564_0]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [hlam, p564_0]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p564_1]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h493, hlam, p564_1]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h495, hlam, p564_1]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h4, hlam, p564_1]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h490, hlam, p564_1]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [hlam, p564_0]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h560, hlam, p564_1]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h495, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p564_1, u2elo4]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h1, h415, h489, hc23, hc35, hlam, hphi, p564_1]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h489, h493, hc23, hc35, hlam, hphi, p564_1]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h560, hc23, hc35, hlam, hphi, p564_1]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [hlam, p564_0]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h489, h491, h495, h562, hc23, hc34, hlam, hphi, p564_1]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h488, hlam, p564_0]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h489, h491, h495, hc23, hc45, hlam, hphi, ht34, p564_1]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h4, h488, h560, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p564_1, u2elo0]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [h562, hlam, p564_0]
                      · have p564_0 := h564c.1
                        have p564_1 := h564c.2.1
                        have p564_2 := h564c.2.2.1
                        have p564_3 := h564c.2.2.2
                        linarith only [hlam, p564_0]
                    · linarith only [h563, hlam, ht01, ht12, u2elo0]
                    · linarith only [h3, h563, hlam, ht01, ht12, u2elo0]
                    · rcases h5bigk with h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c | h592c
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [hlam, p592_0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h4, h489, h491, h495, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p592_1, u2elo0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h4, h560, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p592_1, u2elo0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h415, hlam, p592_1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p592_1, u2elo0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h2, hlam, p592_0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [hlam, p592_0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h2, h560, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p592_1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h493, hlam, p592_1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h495, hlam, p592_1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h4, hlam, p592_1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h490, hlam, p592_1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [hlam, p592_0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h560, hlam, p592_1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h495, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p592_1, u2elo4]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h415, h562, hc03, hc34, hlam, hphi, p592_1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h489, h493, h562, hc23, hc34, hlam, hphi, p592_1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h560, h562, hc23, hc34, hlam, hphi, p592_1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [hlam, p592_0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h489, h491, h495, h562, hc23, hc34, hlam, hphi, p592_1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h488, hlam, p592_0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h489, h491, h495, hc23, hc45, hlam, hphi, ht34, p592_1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h488, h5, h560, hc23, hc34, hlam, hphi, p592_1]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [h562, hlam, p592_0]
                      · have p592_0 := h592c.1
                        have p592_1 := h592c.2.1
                        have p592_2 := h592c.2.2.1
                        have p592_3 := h592c.2.2.2
                        linarith only [hlam, p592_0]
                    · linarith only [h4, h563, hlam, ht01, ht12, u2elo0]
                  · linarith only [h488, h5, h562, hlam]
        · linarith only [h4, h490, hc12, hlam, hphi, u2elo0]
      · linarith only [h3, h489, hc12, hlam, hphi, u2elo0]
    · rcases m.htr 1 2 3 (by decide) (by decide) with h622 | h622
      · rcases m.htr 1 2 5 (by decide) (by decide) with h623 | h623
        · rcases m.htr 1 3 4 (by decide) (by decide) with h624 | h624
          · linarith only [h1, h5, h624, hlam]
          · rcases m.htr 1 3 5 (by decide) (by decide) with h626 | h626
            · linarith only [h1, h415, h626, hlam]
            · rcases m.htr 1 4 5 (by decide) (by decide) with h628 | h628
              · linarith only [h2, h488, h628, hlam]
              · rcases m.htr 2 3 5 (by decide) (by decide) with h630 | h630
                · linarith only [h3, h415, h630, hlam]
                · rcases m.htr 3 4 5 (by decide) (by decide) with h632 | h632
                  · rcases h0emin with h633 | h633 | h633 | h633 | h633
                    · rcases h5bigk with h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c | h634c
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [hlam, p634_0]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h4, h628, hc14, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p634_1, u2elo0]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h4, hc25, hlam, hphi, ht01, ht0b, ht12, ht5b, p634_1, u2elo0]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h415, hlam, p634_1]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h488, hlam, p634_1]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h2, hlam, p634_0]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [hlam, p634_0]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h2, hc01, hc25, hlam, hphi, ht0b, ht5b, p634_1]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h626, hlam, p634_1]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h628, hlam, p634_1]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h4, hlam, p634_1]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h623, hlam, p634_1]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [hlam, p634_0]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h630, hlam, p634_1]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h488, h5, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p634_1, u2elo4]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h1, h415, hc13, hc35, hlam, hphi, p634_1]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h622, h626, hc23, hc35, hlam, hphi, p634_1]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h630, hc23, hc35, hlam, hphi, p634_1]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [hlam, p634_0]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h1, h488, h5, h622, h632, hc23, hc34, hlam, hphi, p634_1]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h1, h488, h5, h622, hc23, hc45, hlam, hphi, ht34, p634_1]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h622, h624, h628, hc23, hc45, hlam, hphi, ht34, p634_1]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h630, h632, hc23, hc34, hlam, hphi, p634_1]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [h632, hlam, p634_0]
                      · have p634_0 := h634c.1
                        have p634_1 := h634c.2.1
                        have p634_2 := h634c.2.2.1
                        have p634_3 := h634c.2.2.2
                        linarith only [hlam, p634_0]
                    · linarith only [h633, hlam, ht01, ht12, u2elo0]
                    · linarith only [h3, h633, hlam, ht01, ht12, u2elo0]
                    · linarith only [h4, h488, h633, hlam, ht01, ht12, u2elo0]
                    · linarith only [h4, h633, hlam, ht01, ht12, u2elo0]
                  · rcases h0emin with h664 | h664 | h664 | h664 | h664
                    · rcases h5bigk with h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c | h665c
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [hlam, p665_0]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h415, h622, h624, h628, hc23, hc35, hlam, hphi, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h4, h630, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p665_1, u2elo0]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h415, hlam, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h488, hlam, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h2, hlam, p665_0]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [hlam, p665_0]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h2, h630, hc01, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h626, hlam, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h628, hlam, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h4, hlam, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h623, hlam, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [hlam, p665_0]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h630, hlam, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h632, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, p665_1, u2elo4]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h1, h415, h622, h632, hc23, hc45, hlam, hphi, ht34, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h622, h626, h632, hc23, hc45, hlam, hphi, ht34, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h630, h632, hc23, hc45, hlam, hphi, ht34, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [hlam, p665_0]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h632, hlam, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h1, h488, h5, h622, hc23, hc45, hlam, hphi, ht34, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h622, h624, h628, hc23, hc45, hlam, hphi, ht34, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h630, hc23, hc45, hlam, hphi, ht34, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [h1, h415, h622, hc23, hc45, hlam, hphi, ht34, p665_1]
                      · have p665_0 := h665c.1
                        have p665_1 := h665c.2.1
                        have p665_2 := h665c.2.2.1
                        have p665_3 := h665c.2.2.2
                        linarith only [hlam, p665_0]
                    · linarith only [h664, hlam, ht01, ht12, u2elo0]
                    · linarith only [h5, h664, hc34, hlam, ht01, ht12, ht23]
                    · linarith only [h4, h488, h664, hlam, ht01, ht12, u2elo0]
                    · linarith only [h4, h664, hlam, ht01, ht12, u2elo0]
        · linarith only [h4, h623, hc12, hlam, hphi, u2elo0]
      · linarith only [h3, h622, hc12, hlam, hphi, u2elo0]

set_option maxHeartbeats 4970000 in
theorem r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 0 2 + m.lam ≤ m.d 2 5 ∧ m.d 0 2 < m.d 0 5 ∧ m.d 0 5 < m.d 2 5))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
  · exact r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x0_x0_x0_x0 m hb0 hb2 hb5 h0 h1 h2 h3 h4 h5
  · exact r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x0_x0_x0_x1 m hb0 hb2 hb5 h0 h1 h2 h3 h4 h5

set_option maxHeartbeats 4970000 in
theorem r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x0_x0_x1 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
    (h4 : (m.d 2 5 + m.lam ≤ m.d 0 2 ∧ m.d 2 5 < m.d 0 5 ∧ m.d 0 5 < m.d 0 2))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 3 4 (by decide) (by decide) with h697 | h697
  · rcases m.htr 0 3 5 (by decide) (by decide) with h698 | h698
    · linarith only [h3, h4, h698, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h700 | h700
      · linarith only [h3, h4, h697, h700, hlam]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h702 | h702
        · rcases m.htr 1 2 5 (by decide) (by decide) with h703 | h703
          · linarith only [h0, h4, h703, hlam]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h705 | h705
            · rcases m.htr 1 3 5 (by decide) (by decide) with h706 | h706
              · linarith only [h1, h698, h706, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h708 | h708
                · linarith only [h1, h3, h4, h700, h705, h708, hc04, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u2elo4]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h710 | h710
                  · linarith only [h0, h4, h698, h702, h710, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h712 | h712
                    · linarith only [h1, h705, h708, h712, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                    · rcases h0emin with h714 | h714 | h714 | h714 | h714
                      · rcases h5bigk with h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c | h715c
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [hlam, p715_0]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p715_1, u2elo4]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [h4, hlam, p715_0]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [h698, hlam, p715_1]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [h700, hlam, p715_1]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [h2, hlam, p715_0]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [hlam, p715_0]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [h703, hlam, p715_0]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [h706, hlam, p715_1]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [h708, hlam, p715_1]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p715_1, u2elo4]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p715_1, u2elo4]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [hlam, p715_0]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [h710, hlam, p715_1]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [h710, h712, hlam, p715_1]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [h0, h4, h702, hc23, hc35, hlam, hphi, p715_1]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [h702, h703, h712, hc23, hc45, hlam, hphi, ht34, p715_1]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [h1, h3, h4, h705, h712, hc34, hc45, hlam, hphi, p715_1]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [hlam, p715_0]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [h712, hlam, p715_1]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [h1, h3, h4, h705, hc34, hc45, hlam, hphi, p715_1]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [h702, h703, hc23, hc45, hlam, hphi, ht34, p715_1]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [h1, h3, h4, h705, hc34, hc45, hlam, hphi, p715_1]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [h1, h698, h705, hc34, hc45, hlam, hphi, p715_1]
                        · have p715_0 := h715c.1
                          have p715_1 := h715c.2.1
                          have p715_2 := h715c.2.2.1
                          have p715_3 := h715c.2.2.2
                          linarith only [hlam, p715_0]
                      · linarith only [h4, h714, hlam, ht01, ht12, u2elo4]
                      · linarith only [h3, h4, h714, hlam, ht01, ht12, u2elo4]
                      · linarith only [h3, h4, h697, h714, hlam, ht01, ht12, u2elo4]
                      · linarith only [h4, h714, hlam, ht01, ht12, u2elo4]
            · linarith only [h3, h4, h697, h705, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
        · linarith only [h3, h4, h702, hc12, hlam, hphi, u2elo4]
  · rcases m.htr 0 3 5 (by decide) (by decide) with h747 | h747
    · linarith only [h3, h4, h747, hlam]
    · rcases m.htr 0 4 5 (by decide) (by decide) with h749 | h749
      · rcases m.htr 1 2 3 (by decide) (by decide) with h750 | h750
        · rcases m.htr 1 2 5 (by decide) (by decide) with h751 | h751
          · linarith only [h4, h751, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h753 | h753
            · linarith only [h1, h697, h753, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h755 | h755
              · linarith only [h1, h747, h755, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h757 | h757
                · rcases m.htr 2 3 5 (by decide) (by decide) with h758 | h758
                  · linarith only [h0, h1, h4, h747, h750, h758, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u2elo4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h760 | h760
                    · rcases h0emin with h761 | h761 | h761 | h761 | h761
                      · rcases h5bigk with h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c | h762c
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p762_1, u2elo4]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h4, hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h747, hlam, p762_1]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p762_1, u2elo4]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h2, hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h751, hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h755, hlam, p762_1]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p762_1]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p762_1, u2elo4]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p762_1, u2elo4]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h758, hlam, p762_1]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p762_1, u2elo4]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h2, h750, h751, h760, hc23, hc34, hlam, hphi, p762_1]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h750, h751, h760, hc23, hc34, hlam, hphi, p762_1]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h0, h4, h750, h760, hc23, hc34, hlam, hphi, p762_1]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          rcases p762_3 (m.d 0 5) (by simp) with h782 | h782
                          · linarith only [h747, h782, hlam]
                          · linarith only [h749, h782, hlam]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h749, hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h757, hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h0, h4, h750, hc23, hc45, hlam, hphi, ht34, p762_1]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [h760, hlam, p762_0]
                        · have p762_0 := h762c.1
                          have p762_1 := h762c.2.1
                          have p762_2 := h762c.2.2.1
                          have p762_3 := h762c.2.2.2
                          linarith only [hlam, p762_0]
                      · linarith only [h4, h761, hlam, ht01, ht12, u2elo4]
                      · linarith only [h3, h4, h761, hlam, ht01, ht12, u2elo4]
                      · rcases h5bigk with h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c | h792c
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [hlam, p792_0]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [h4, h757, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p792_1, u2elo4]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [h4, hlam, p792_0]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [h747, hlam, p792_1]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p792_1, u2elo4]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [h2, hlam, p792_0]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [hlam, p792_0]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [h751, hlam, p792_0]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [h755, hlam, p792_1]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [h2, hc01, hc45, hlam, hphi, ht0b, ht5b, p792_1]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p792_1, u2elo4]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p792_1, u2elo4]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [hlam, p792_0]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [h758, hlam, p792_1]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p792_1, u2elo4]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [h2, h750, h751, h760, hc23, hc34, hlam, hphi, p792_1]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [h750, h751, h760, hc23, hc34, hlam, hphi, p792_1]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [h4, h760, hc02, hc34, hlam, hphi, ht23, p792_1]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [hlam, p792_0]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          rcases p792_3 (m.d 0 5) (by simp) with h812 | h812
                          · linarith only [h747, h812, hlam]
                          · linarith only [h749, h812, hlam]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [h749, hlam, p792_0]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [h757, hlam, p792_0]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [h0, h4, h750, hc23, hc45, hlam, hphi, ht34, p792_1]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [h760, hlam, p792_0]
                        · have p792_0 := h792c.1
                          have p792_1 := h792c.2.1
                          have p792_2 := h792c.2.2.1
                          have p792_3 := h792c.2.2.2
                          linarith only [hlam, p792_0]
                      · linarith only [h4, h761, hlam, ht01, ht12, u2elo4]
                    · linarith only [h697, h749, h760, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h822 | h822
                  · linarith only [h0, h4, h750, h822, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h824 | h824
                    · rcases h0emin with h825 | h825 | h825 | h825 | h825
                      · rcases h5bigk with h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c | h826c
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [hlam, p826_0]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [h4, hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p826_1, u2elo4]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [h4, hlam, p826_0]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [h747, hlam, p826_1]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [h4, h753, h757, hc13, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p826_1, u2elo4]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [h2, hlam, p826_0]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [hlam, p826_0]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [h751, hlam, p826_0]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [h755, hlam, p826_1]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [h757, hlam, p826_1]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p826_1, u2elo4]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p826_1, u2elo4]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [hlam, p826_0]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [h822, hlam, p826_1]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [h750, h753, h757, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p826_1, u2elo4]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [h4, hc02, hc35, hlam, hphi, ht23, p826_1]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [h750, h751, hc23, hc35, hlam, hphi, p826_1]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [h0, h4, h750, hc23, hc35, hlam, hphi, p826_1]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [hlam, p826_0]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [h750, h753, h757, h824, hc23, hc34, hlam, hphi, p826_1]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [h749, hlam, p826_0]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [h749, h750, h751, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p826_1]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [h0, h4, h697, h749, h750, hc23, hc34, hlam, hphi, p826_1]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [h824, hlam, p826_0]
                        · have p826_0 := h826c.1
                          have p826_1 := h826c.2.1
                          have p826_2 := h826c.2.2.1
                          have p826_3 := h826c.2.2.2
                          linarith only [hlam, p826_0]
                      · linarith only [h4, h825, hlam, ht01, ht12, u2elo4]
                      · linarith only [h3, h4, h825, hlam, ht01, ht12, u2elo4]
                      · rcases h5bigk with h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c | h854c
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h4, h750, h751, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p854_1, u2elo4]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h4, hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h747, hlam, p854_1]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h4, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p854_1, u2elo4]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h2, hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h751, hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h755, hlam, p854_1]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h757, hlam, p854_1]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p854_1, u2elo4]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h750, h751, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p854_1, u2elo4]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h822, hlam, p854_1]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h750, h753, h757, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p854_1, u2elo4]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h4, h824, hc02, hc34, hlam, hphi, ht23, p854_1]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h750, h751, h824, hc23, hc34, hlam, hphi, p854_1]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h0, h4, h750, h824, hc23, hc34, hlam, hphi, p854_1]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h750, h753, h757, h824, hc23, hc34, hlam, hphi, p854_1]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h749, hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h749, h750, h751, hc05, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p854_1]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h0, h4, h697, h749, h750, hc23, hc34, hlam, hphi, p854_1]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [h824, hlam, p854_0]
                        · have p854_0 := h854c.1
                          have p854_1 := h854c.2.1
                          have p854_2 := h854c.2.2.1
                          have p854_3 := h854c.2.2.2
                          linarith only [hlam, p854_0]
                      · linarith only [h4, h825, hlam, ht01, ht12, u2elo4]
                    · linarith only [h697, h749, h824, hlam]
        · linarith only [h3, h4, h750, hc12, hlam, hphi, u2elo4]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h883 | h883
        · rcases m.htr 1 2 5 (by decide) (by decide) with h884 | h884
          · linarith only [h4, h884, hc02, hlam, hphi, u2elo1]
          · rcases m.htr 1 3 4 (by decide) (by decide) with h886 | h886
            · linarith only [h1, h697, h886, hlam]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h888 | h888
              · linarith only [h1, h747, h888, hlam]
              · rcases m.htr 1 4 5 (by decide) (by decide) with h890 | h890
                · linarith only [h2, h749, h890, hlam]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h892 | h892
                  · linarith only [h0, h4, h883, h892, hc35, hlam, hphi, ht01, ht0b, ht12, ht5b, u2elo4]
                  · rcases m.htr 3 4 5 (by decide) (by decide) with h894 | h894
                    · rcases h0emin with h895 | h895 | h895 | h895 | h895
                      · rcases h5bigk with h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c | h896c
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [hlam, p896_0]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h0, h4, h749, h883, h894, hc15, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht5b, p896_1, u2elo4]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h4, hlam, p896_0]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h747, hlam, p896_1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h749, hlam, p896_1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h2, hlam, p896_0]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [hlam, p896_0]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h884, hlam, p896_0]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h888, hlam, p896_1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h890, hlam, p896_1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p896_1, u2elo4]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [hc15, hlam, hphi, ht01, ht0b, ht12, ht5b, p896_1, u2elo4]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [hlam, p896_0]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h892, hlam, p896_1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h697, h749, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p896_1, u2elo4]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h4, hc02, hc35, hlam, hphi, ht23, p896_1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h883, h884, hc23, hc35, hlam, hphi, p896_1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h0, h4, h883, hc23, hc35, hlam, hphi, p896_1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [hlam, p896_0]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h0, h4, h749, h883, h894, hc23, hc34, hlam, hphi, p896_1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h0, h4, h883, hc23, hc45, hlam, hphi, ht34, p896_1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h883, h884, hc23, hc45, hlam, hphi, ht34, p896_1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h0, h4, h883, h894, hc23, hc34, hlam, hphi, p896_1]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [h894, hlam, p896_0]
                        · have p896_0 := h896c.1
                          have p896_1 := h896c.2.1
                          have p896_2 := h896c.2.2.1
                          have p896_3 := h896c.2.2.2
                          linarith only [hlam, p896_0]
                      · linarith only [h4, h895, hlam, ht01, ht12, u2elo4]
                      · linarith only [h3, h4, h895, hlam, ht01, ht12, u2elo4]
                      · linarith only [h0, h4, h749, h883, h894, h895, hc23, hc34, hlam, hphi, ht01, ht12, u2elo4]
                      · linarith only [h4, h895, hlam, ht01, ht12, u2elo4]
                    · rcases h0emin with h926 | h926 | h926 | h926 | h926
                      · rcases h5bigk with h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c | h927c
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [hlam, p927_0]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [h4, h883, h884, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p927_1, u2elo4]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [h4, hlam, p927_0]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [h747, hlam, p927_1]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [h749, hlam, p927_1]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [h2, hlam, p927_0]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [hlam, p927_0]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [h884, hlam, p927_0]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [h888, hlam, p927_1]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [h890, hlam, p927_1]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [hc05, hlam, hphi, ht01, ht0b, ht12, ht5b, p927_1, u2elo4]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [h883, h884, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p927_1, u2elo4]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [hlam, p927_0]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [h892, hlam, p927_1]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [h697, h894, hc03, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p927_1, u2elo4]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [h2, h883, h884, hc23, hc35, hlam, hphi, p927_1]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [h883, h884, h894, hc23, hc45, hlam, hphi, ht34, p927_1]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [h4, h894, hc02, hc45, hlam, hphi, ht23, ht34, p927_1]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [hlam, p927_0]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [h894, hlam, p927_1]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [h2, h883, h884, hc23, hc45, hlam, hphi, ht34, p927_1]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [h883, h884, hc23, hc45, hlam, hphi, ht34, p927_1]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [h0, h4, h883, hc23, hc45, hlam, hphi, ht34, p927_1]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [h1, h747, h883, hc23, hc45, hlam, hphi, ht34, p927_1]
                        · have p927_0 := h927c.1
                          have p927_1 := h927c.2.1
                          have p927_2 := h927c.2.2.1
                          have p927_3 := h927c.2.2.2
                          linarith only [hlam, p927_0]
                      · linarith only [h4, h926, hlam, ht01, ht12, u2elo4]
                      · linarith only [h0, h4, h697, h883, h926, hc23, hc34, hlam, hphi, ht01, ht12, u2elo4]
                      · linarith only [h4, h749, h926, hlam, ht01, ht12, u2elo4]
                      · linarith only [h4, h926, hlam, ht01, ht12, u2elo4]
        · linarith only [h3, h4, h883, hc12, hlam, hphi, u2elo4]

set_option maxHeartbeats 4970000 in
theorem r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x0_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_0 m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    (h1 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
    (h2 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
    (h3 : (m.d 0 2 + m.lam ≤ m.d 2 3 ∧ m.d 0 2 < m.d 0 3 ∧ m.d 0 3 < m.d 2 3))
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
  have hc25 := m.hcor 2 5 (by decide)
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0emin := hb0.2.1
  have h2elo := hb2.1
  have h5bigk := hb5.1
  have u2elo0 := h2elo (m.d 0 2) (by simp)
  have u2elo1 := h2elo (m.d 1 2) (by simp)
  have u2elo2 := h2elo (m.d 2 3) (by simp)
  have u2elo4 := h2elo (m.d 2 5) (by simp)
  rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
  · exact r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x0_x0_x0 m hb0 hb2 hb5 h0 h1 h2 h3 h4
  · exact r1l7_10_12_25_L_I_L_0_H_I_x0_x0_x0_x0_x1 m hb0 hb2 hb5 h0 h1 h2 h3 h4

end R2N4
